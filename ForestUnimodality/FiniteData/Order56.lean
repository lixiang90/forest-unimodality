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

theorem case_56_28_1_checked :
    (Witness.rising).check 56 28 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_28_2_checked :
    (Witness.rising).check 56 28 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_28_3_checked :
    (Witness.rising).check 56 28 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_28_4_checked :
    (Witness.rising).check 56 28 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_28_5_checked :
    (Witness.rising).check 56 28 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_28_6_checked :
    (Witness.rising).check 56 28 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_28_7_checked :
    (Witness.rising).check 56 28 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_28_8_checked :
    (Witness.rising).check 56 28 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_28_9_checked :
    (Witness.rising).check 56 28 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_28_10_checked :
    (Witness.rising).check 56 28 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_28_11 : Certificate := {
  objectiveScale := 1298584566072000000
  eta := 1202957233522429097512800
  rows := #[⟨.count 2, 774402180614193153422400⟩, ⟨.count 4, 6825676024935310967424⟩, ⟨.count 5, 923079522346860879000⟩, ⟨.count 6, 142012234207209366000⟩, ⟨.count 7, 25696917320181995160⟩, ⟨.count 8, 5628100138277809920⟩, ⟨.count 9, 1778240150072882496⟩, ⟨.count 10, 1297519726727820960⟩, ⟨.count 12, 152927429486832000⟩, ⟨.path 11, 482588056616866200⟩, ⟨.path 12, 153543297877089120⟩, ⟨.hall 2 1, 635457410665859509728⟩, ⟨.hall 10 1, 9314670705107040⟩, ⟨.hall 9 3, 1427612310493551⟩, ⟨.hall 8 4, 309716662748584⟩, ⟨.hall 8 5, 417074807691360⟩, ⟨.hall 7 7, 236921661591342⟩, ⟨.hall 7 8, 28636760300176⟩, ⟨.hall 2 11, 575601852651826⟩, ⟨.hall 6 11, 108692801302350⟩, ⟨.hall 6 12, 65731295241468⟩, ⟨.hall 10 17, 4726847820502080⟩, ⟨.hall 9 18, 9217353249979056⟩, ⟨.hall 5 22, 98955771314240961120⟩, ⟨.hall 4 23, 64000180216049020944⟩]
  caps := #[0, 1183658264479704756600, 58635158137469456400, 0, 1603479777760995552, 0, 0, 37840589429532120, 58611427337280, 2932472615983704, 1064839344179040, 1314212479453080, 615868390257120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_28_11_checked :
    (Witness.linear .positive case_56_28_11).check 56 28 11 = true := by
  change case_56_28_11.check 56 28 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_28_12 : Certificate := {
  objectiveScale := 864048120000000
  eta := 1347073024657520160000
  rows := #[⟨.count 2, 1070590443979356300000⟩, ⟨.count 4, 11713011029215816320⟩, ⟨.count 5, 1727016698278872000⟩, ⟨.count 6, 280744501918280400⟩, ⟨.count 7, 52959570029566200⟩, ⟨.count 8, 11376921596040000⟩, ⟨.count 9, 2980753458162480⟩, ⟨.count 10, 1077813624888000⟩, ⟨.count 11, 863581534015200⟩, ⟨.count 13, 142710507739800⟩, ⟨.path 12, 219740537016000⟩, ⟨.path 13, 141507066600900⟩, ⟨.privateRow 11 2, 3077091367350⟩, ⟨.hall 2 1, 496357391801631360⟩, ⟨.hall 11 1, 8206392319125⟩, ⟨.hall 10 3, 1346288623680⟩, ⟨.hall 9 4, 928704332556⟩, ⟨.hall 2 5, 273286899714400⟩, ⟨.hall 9 5, 237193915530⟩, ⟨.hall 8 6, 430778814180⟩, ⟨.hall 8 7, 124182481500⟩, ⟨.hall 7 9, 246558672360⟩, ⟨.hall 7 10, 49741412700⟩, ⟨.hall 6 14, 332169322485⟩, ⟨.hall 6 15, 1259000703675⟩, ⟨.hall 11 16, 3443994153600⟩, ⟨.hall 5 22, 147533391052647600⟩, ⟨.hall 4 23, 63004127696469960⟩]
  caps := #[0, 1807589528222634000, 231569952874260000, 0, 3420805890181680, 794300840494200, 105207105603600, 133843182946200, 14418317964960, 20180109811680, 5975032128000, 3509503023000, 2850227515200, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_28_12_checked :
    (Witness.linear .positive case_56_28_12).check 56 28 12 = true := by
  change case_56_28_12.check 56 28 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_28_13 : Certificate := {
  objectiveScale := 36036000000
  eta := 75455273625732000
  rows := #[⟨.count 2, 67951857273300000⟩, ⟨.count 4, 853763920289280⟩, ⟨.count 5, 145179916081200⟩, ⟨.count 6, 26388200638800⟩, ⟨.count 7, 5304178479600⟩, ⟨.count 8, 1196553758400⟩, ⟨.count 9, 310079689920⟩, ⟨.count 10, 97037740800⟩, ⟨.count 11, 39758518800⟩, ⟨.count 12, 36151315200⟩, ⟨.path 13, 3687834150⟩, ⟨.path 14, 8383069695⟩, ⟨.privateRow 9 10, 14200346160⟩, ⟨.privateRow 10 7, 3657293640⟩, ⟨.privateRow 10 8, 4340634480⟩, ⟨.privateRow 11 4, 568854000⟩, ⟨.privateRow 11 5, 56548800⟩, ⟨.privateRow 12 2, 1199758560⟩, ⟨.privateRow 13 15, 327026700⟩, ⟨.privateRow 14 0, 558257700⟩, ⟨.privateRow 17 0, 13213200⟩, ⟨.privateRow 20 8, 3491888400⟩, ⟨.privateRow 21 6, 4655851200⟩, ⟨.hall 2 1, 61370171422560⟩, ⟨.hall 12 1, 933512580⟩, ⟨.hall 14 1, 558918360⟩, ⟨.hall 15 1, 495495000⟩, ⟨.hall 16 1, 630630000⟩, ⟨.hall 17 1, 1114953840⟩, ⟨.hall 18 1, 698377680⟩, ⟨.hall 19 1, 756575820⟩, ⟨.hall 12 2, 27464580⟩, ⟨.hall 16 2, 10090080⟩, ⟨.hall 11 3, 83526300⟩, ⟨.hall 20 3, 2876650920⟩, ⟨.hall 21 3, 15102417330⟩, ⟨.hall 10 4, 110192940⟩, ⟨.hall 19 4, 701703288⟩, ⟨.hall 22 4, 332893360800⟩, ⟨.hall 23 4, 7656547298400⟩, ⟨.hall 18 5, 196911000⟩, ⟨.hall 20 5, 1136249400⟩, ⟨.hall 9 6, 46902240⟩, ⟨.hall 19 6, 232792560⟩, ⟨.hall 21 6, 151897145400⟩, ⟨.hall 20 7, 22115293200⟩, ⟨.hall 8 8, 35025760⟩, ⟨.hall 7 10, 6003900⟩, ⟨.hall 17 10, 6126120000⟩, ⟨.hall 7 11, 32529420⟩, ⟨.hall 16 11, 3527924400⟩, ⟨.hall 15 12, 2437835400⟩, ⟨.hall 6 16, 171600⟩, ⟨.hall 6 17, 2039414520⟩, ⟨.hall 2 18, 447206760⟩, ⟨.hall 5 22, 15806032842600⟩, ⟨.hall 4 23, 8510546804760⟩]
  caps := #[0, 192451064305500, 0, 1271629359000, 0, 85890754950, 15178041450, 0, 2909907000, 0, 0, 811991400, 0, 0, 129444315, 0, 0, 422822400, 0, 0, 10475665200, 0, 6401795400, 0, 0, 0, 0, 0, 0] }

theorem case_56_28_13_checked :
    (Witness.linear .positive case_56_28_13).check 56 28 13 = true := by
  change case_56_28_13.check 56 28 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_28_14 : Certificate := {
  objectiveScale := 3284531250
  eta := 5943394840383000
  rows := #[⟨.count 2, 11542245052338000⟩, ⟨.count 4, 187644305328480⟩, ⟨.count 5, 33914578097400⟩, ⟨.count 6, 6555438489600⟩, ⟨.count 7, 1360672513200⟩, ⟨.count 8, 303406303200⟩, ⟨.count 9, 77519922480⟩, ⟨.count 10, 21870248400⟩, ⟨.count 11, 7524917400⟩, ⟨.count 12, 3250447200⟩, ⟨.count 13, 3285131850⟩, ⟨.path 15, 901991090⟩, ⟨.path 16, 30836960⟩, ⟨.privateRow 9 11, 155195040⟩, ⟨.privateRow 9 12, 446185740⟩, ⟨.privateRow 10 9, 1043890848⟩, ⟨.privateRow 10 10, 1937895960⟩, ⟨.privateRow 10 11, 48243195⟩, ⟨.privateRow 11 6, 124224100⟩, ⟨.privateRow 11 7, 608899200⟩, ⟨.privateRow 11 8, 278738460⟩, ⟨.privateRow 12 4, 172788000⟩, ⟨.privateRow 12 5, 325375050⟩, ⟨.privateRow 13 2, 106531425⟩, ⟨.privateRow 14 14, 38648610⟩, ⟨.privateRow 15 0, 64414350⟩, ⟨.privateRow 15 13, 4294290⟩, ⟨.privateRow 16 0, 2286900⟩, ⟨.privateRow 18 5, 64664600⟩, ⟨.privateRow 19 4, 39819780⟩, ⟨.privateRow 19 5, 69837768⟩, ⟨.privateRow 19 6, 9189180⟩, ⟨.privateRow 19 7, 61261200⟩, ⟨.privateRow 19 8, 220540320⟩, ⟨.privateRow 19 9, 588107520⟩, ⟨.privateRow 20 7, 775975200⟩, ⟨.privateRow 21 1, 41570100⟩, ⟨.hall 2 1, 2640527209320⟩, ⟨.hall 13 1, 92633970⟩, ⟨.hall 15 1, 47072025⟩, ⟨.hall 16 1, 72072000⟩, ⟨.hall 17 1, 69429360⟩, ⟨.hall 18 1, 138858720⟩, ⟨.hall 19 1, 315239925⟩, ⟨.hall 20 1, 900685500⟩, ⟨.hall 21 1, 1115464350⟩, ⟨.hall 13 2, 5190900⟩, ⟨.hall 19 2, 16628040⟩, ⟨.hall 22 2, 8108940840⟩, ⟨.hall 23 2, 62168546440⟩, ⟨.hall 24 2, 746022557280⟩, ⟨.hall 25 2, 18650563932000⟩, ⟨.hall 12 3, 11586960⟩, ⟨.hall 21 3, 1105764660⟩, ⟨.hall 11 4, 3869580⟩, ⟨.hall 11 5, 3276075⟩, ⟨.hall 2 6, 1409226390⟩, ⟨.hall 10 6, 6612375⟩, ⟨.hall 20 6, 415701000⟩, ⟨.hall 17 7, 5870865⟩, ⟨.hall 9 8, 5310480⟩, ⟨.hall 15 9, 1261260⟩, ⟨.hall 16 9, 6726720⟩, ⟨.hall 8 10, 6494880⟩, ⟨.hall 7 14, 21676655⟩, ⟨.hall 7 15, 20120100⟩, ⟨.hall 5 21, 67024857900⟩, ⟨.hall 6 21, 1678725348300⟩, ⟨.hall 0 23, 220861941300⟩]
  caps := #[0, 24669609564600, 0, 98961709000, 0, 0, 2291168880, 830154325, 387987600, 0, 78896510, 4393480, 53172350, 0, 42202160, 10290280, 65140460, 0, 10210200, 0, 0, 2868336900, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_28_14_checked :
    (Witness.linear .positive case_56_28_14).check 56 28 14 = true := by
  change case_56_28_14.check 56 28 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_28_15 : Certificate := {
  objectiveScale := 12012000000
  eta := 40311721526076000
  rows := #[⟨.count 2, 49729274703108000⟩, ⟨.count 4, 859417985986560⟩, ⟨.count 5, 186996443634000⟩, ⟨.count 6, 41137937240400⟩, ⟨.count 7, 10266151896000⟩, ⟨.count 8, 2551406457600⟩, ⟨.count 9, 708154967520⟩, ⟨.count 10, 210616005600⟩, ⟨.count 11, 68735066400⟩, ⟨.count 12, 25210785600⟩, ⟨.count 13, 11981069100⟩, ⟨.count 14, 11903771880⟩, ⟨.path 16, 996848160⟩, ⟨.path 17, 1756921320⟩, ⟨.privateRow 5 23, 8451650287080⟩, ⟨.privateRow 10 10, 3099816720⟩, ⟨.privateRow 11 9, 16751534800⟩, ⟨.privateRow 11 10, 6585579000⟩, ⟨.privateRow 12 6, 1754953200⟩, ⟨.privateRow 12 7, 2366484120⟩, ⟨.privateRow 13 4, 1104953850⟩, ⟨.privateRow 13 5, 2259457200⟩, ⟨.privateRow 16 0, 77754600⟩, ⟨.privateRow 17 0, 145345200⟩, ⟨.privateRow 18 2, 34034000⟩, ⟨.privateRow 18 3, 15315300⟩, ⟨.privateRow 20 1, 87297210⟩, ⟨.privateRow 20 2, 99768240⟩, ⟨.privateRow 21 1, 166280400⟩, ⟨.privateRow 21 2, 96996900⟩, ⟨.privateRow 24 4, 1060137318240⟩, ⟨.hall 2 1, 38164943456640⟩, ⟨.hall 14 1, 128828700⟩, ⟨.hall 15 1, 148648500⟩, ⟨.hall 17 1, 42882840⟩, ⟨.hall 18 1, 85765680⟩, ⟨.hall 19 1, 203693490⟩, ⟨.hall 20 1, 748261800⟩, ⟨.hall 14 2, 127507380⟩, ⟨.hall 18 2, 42882840⟩, ⟨.hall 13 3, 141074505⟩, ⟨.hall 17 3, 3573570⟩, ⟨.hall 19 4, 23279256⟩, ⟨.hall 12 5, 53271900⟩, ⟨.hall 21 5, 10475665200⟩, ⟨.hall 22 5, 230464634400⟩, ⟨.hall 11 6, 71572050⟩, ⟨.hall 17 6, 1458600⟩, ⟨.hall 20 7, 13967553600⟩, ⟨.hall 10 8, 59431680⟩, ⟨.hall 19 8, 4190266080⟩, ⟨.hall 9 9, 50728356⟩, ⟨.hall 18 9, 1764322560⟩, ⟨.hall 9 10, 29247120⟩, ⟨.hall 17 10, 735134400⟩, ⟨.hall 2 11, 92162070⟩, ⟨.hall 8 12, 128625420⟩, ⟨.hall 8 13, 38721540⟩, ⟨.hall 13 14, 386486100⟩, ⟨.hall 7 16, 2661739080⟩, ⟨.hall 6 21, 17955290152800⟩, ⟨.hall 5 22, 17329660147800⟩]
  caps := #[0, 0, 36622925539200, 0, 0, 10708457760, 0, 0, 1383962580, 698377680, 113430240, 0, 0, 42042000, 531170640, 20614440, 0, 39205320, 464904440, 2095133040, 602766450, 5293259400, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_28_15_checked :
    (Witness.linear .positive case_56_28_15).check 56 28 15 = true := by
  change case_56_28_15.check 56 28 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_28_16 : Certificate := {
  objectiveScale := 1663200000
  eta := 42999169627814400
  rows := #[⟨.count 3, 399318389870400⟩, ⟨.count 4, 121138357564224⟩, ⟨.count 5, 30125568793320⟩, ⟨.count 6, 7467054154560⟩, ⟨.count 7, 2087450885520⟩, ⟨.count 8, 603398315520⟩, ⟨.count 9, 184371707520⟩, ⟨.count 10, 60207507360⟩, ⟨.count 11, 20620519920⟩, ⟨.count 12, 8467018560⟩, ⟨.count 13, 3942158220⟩, ⟨.count 14, 2597186592⟩, ⟨.count 15, 2628105480⟩, ⟨.path 16, 332640000⟩, ⟨.privateRow 11 9, 1155794640⟩, ⟨.privateRow 12 7, 618377760⟩, ⟨.privateRow 12 8, 1942340400⟩, ⟨.privateRow 12 9, 713512800⟩, ⟨.privateRow 13 5, 50270220⟩, ⟨.privateRow 14 3, 137417280⟩, ⟨.privateRow 14 4, 141945804⟩, ⟨.privateRow 15 13, 365873508⟩, ⟨.privateRow 17 0, 138738600⟩, ⟨.privateRow 24 3, 120737861244⟩, ⟨.hall 15 1, 185315130⟩, ⟨.hall 17 1, 221765544⟩, ⟨.hall 18 1, 443531088⟩, ⟨.hall 19 1, 797314518⟩, ⟨.hall 20 1, 465585120⟩, ⟨.hall 21 1, 1629547920⟩, ⟨.hall 22 1, 7170010848⟩, ⟨.hall 23 1, 2944825884⟩, ⟨.hall 1 2, 2885929366320⟩, ⟨.hall 2 2, 105032123196⟩, ⟨.hall 14 2, 73333260⟩, ⟨.hall 23 2, 100124080056⟩, ⟨.hall 24 2, 1283944085424⟩, ⟨.hall 25 2, 32098602135600⟩, ⟨.hall 14 3, 4990986⟩, ⟨.hall 20 3, 508818024⟩, ⟨.hall 21 3, 2671294626⟩, ⟨.hall 22 3, 19589493924⟩, ⟨.hall 13 4, 24504480⟩, ⟨.hall 12 5, 29503980⟩, ⟨.hall 11 7, 19214811⟩, ⟨.hall 10 8, 19414584⟩, ⟨.hall 19 8, 2048574528⟩, ⟨.hall 10 9, 4774392⟩, ⟨.hall 9 10, 23337216⟩, ⟨.hall 9 11, 7833672⟩, ⟨.hall 15 11, 1981980⟩, ⟨.hall 1 12, 46378332⟩, ⟨.hall 8 13, 74204988⟩, ⟨.hall 8 14, 33061028⟩, ⟨.hall 7 16, 823734912⟩, ⟨.hall 6 21, 5699460246480⟩, ⟨.hall 5 22, 6520868794440⟩, ⟨.hall 4 23, 4735280021472⟩, ⟨.assumptionRow 16, 2624646024⟩]
  caps := #[0, 0, 0, 389211253200, 95387646816, 0, 3631563936, 929728800, 232792560, 0, 0, 22968792, 0, 648648, 95147052, 0, 20507256, 0, 0, 0, 232792560, 0, 0, 0, 41227562376, 0, 0, 0, 0] }

theorem case_56_28_16_checked :
    (Witness.linear .conditional case_56_28_16).check 56 28 16 = true := by
  change case_56_28_16.check 56 28 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_28_17 : Certificate := {
  objectiveScale := 9240000000
  eta := 68736653371386000
  rows := #[⟨.count 3, 1095475228848000⟩, ⟨.count 4, 301785756592320⟩, ⟨.count 5, 87166846166400⟩, ⟨.count 6, 26042503687200⟩, ⟨.count 7, 7992932547600⟩, ⟨.count 8, 2523471350400⟩, ⟨.count 9, 873670477680⟩, ⟨.count 10, 323091568800⟩, ⟨.count 11, 126688161600⟩, ⟨.count 12, 50897246400⟩, ⟨.count 13, 22802679900⟩, ⟨.count 14, 10460890440⟩, ⟨.count 15, 9275666400⟩, ⟨.count 16, 8562153600⟩, ⟨.path 15, 972972000⟩, ⟨.privateRow 4 24, 30390603122880⟩, ⟨.privateRow 14 4, 96035940⟩, ⟨.privateRow 15 3, 1323422100⟩, ⟨.privateRow 15 4, 1123386264⟩, ⟨.privateRow 18 0, 840949200⟩, ⟨.privateRow 20 5, 1920538620⟩, ⟨.privateRow 20 7, 1978736760⟩, ⟨.privateRow 26 2, 167855075388000⟩, ⟨.hall 1 1, 67730995332000⟩, ⟨.hall 16 1, 983782800⟩, ⟨.hall 18 1, 1592791200⟩, ⟨.hall 19 1, 1338557220⟩, ⟨.hall 20 1, 415701000⟩, ⟨.hall 15 2, 491891400⟩, ⟨.hall 20 2, 1829084400⟩, ⟨.hall 21 2, 9893683800⟩, ⟨.hall 20 3, 399072960⟩, ⟨.hall 22 3, 72980467560⟩, ⟨.hall 23 3, 839275376940⟩, ⟨.hall 24 3, 20142609046560⟩, ⟨.hall 13 4, 93848040⟩, ⟨.hall 14 4, 134558424⟩, ⟨.hall 13 5, 141608610⟩, ⟨.hall 19 5, 141338340⟩, ⟨.hall 12 6, 179322660⟩, ⟨.hall 21 6, 48886437600⟩, ⟨.hall 11 7, 78742125⟩, ⟨.hall 12 7, 18641700⟩, ⟨.hall 20 7, 11057646600⟩, ⟨.hall 11 8, 117431160⟩, ⟨.hall 1 9, 91891800⟩, ⟨.hall 10 9, 131919480⟩, ⟨.hall 10 10, 98837550⟩, ⟨.hall 9 11, 131385870⟩, ⟨.hall 16 11, 118918800⟩, ⟨.hall 9 12, 307638540⟩, ⟨.hall 15 12, 594594000⟩, ⟨.hall 8 14, 377937560⟩, ⟨.hall 8 15, 3351588240⟩, ⟨.hall 7 20, 27766914575400⟩, ⟨.hall 5 21, 2221132013100⟩, ⟨.hall 6 21, 39708008940600⟩, ⟨.hall 4 23, 45585904684320⟩, ⟨.assumptionRow 17, 8422777440⟩]
  caps := #[0, 165143315937600, 0, 166942110720, 237233525760, 32376072960, 0, 4888643760, 17297280, 687063300, 0, 0, 50930880, 143663520, 63580440, 152948796, 82827360, 0, 379402800, 0, 349188840, 0, 38410772400, 0, 0, 0, 0, 0, 0] }

theorem case_56_28_17_checked :
    (Witness.linear .conditional case_56_28_17).check 56 28 17 = true := by
  change case_56_28_17.check 56 28 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_28_18 : Certificate := {
  objectiveScale := 13860000000
  eta := 8785888024914000
  rows := #[⟨.count 2, 2603226081456000⟩, ⟨.count 3, 795102988680000⟩, ⟨.count 4, 247365374256000⟩, ⟨.count 5, 77743403337600⟩, ⟨.count 6, 24698126653200⟩, ⟨.count 7, 7895159672400⟩, ⟨.count 8, 2886627744000⟩, ⟨.count 9, 1055947052160⟩, ⟨.count 10, 385945560000⟩, ⟨.count 11, 139491752400⟩, ⟨.count 12, 62789126400⟩, ⟨.count 13, 27826999200⟩, ⟨.count 14, 13707373680⟩, ⟨.count 15, 8116208100⟩, ⟨.count 16, 6659452800⟩, ⟨.count 17, 6738732000⟩, ⟨.path 14, 163438275⟩, ⟨.path 15, 1322461140⟩, ⟨.privateRow 3 25, 55951691796000⟩, ⟨.privateRow 15 4, 1324359036⟩, ⟨.privateRow 19 0, 1389404016⟩, ⟨.privateRow 26 2, 157548184794000⟩, ⟨.privateRow 27 1, 76565472984000⟩, ⟨.hall 17 1, 1415133720⟩, ⟨.hall 19 1, 3113600490⟩, ⟨.hall 20 1, 5902954200⟩, ⟨.hall 16 2, 731530800⟩, ⟨.hall 21 2, 9311702400⟩, ⟨.hall 22 2, 45452747340⟩, ⟨.hall 23 2, 265034329560⟩, ⟨.hall 15 3, 616215600⟩, ⟨.hall 24 3, 18905782175280⟩, ⟨.hall 14 4, 192216024⟩, ⟨.hall 23 4, 1590205977360⟩, ⟨.hall 13 5, 89137620⟩, ⟨.hall 14 5, 214534320⟩, ⟨.hall 22 5, 230464634400⟩, ⟨.hall 13 6, 311591280⟩, ⟨.hall 21 6, 47140493400⟩, ⟨.hall 12 7, 321487320⟩, ⟨.hall 20 7, 20951330400⟩, ⟨.hall 11 8, 122239040⟩, ⟨.hall 12 8, 80531220⟩, ⟨.hall 11 9, 338433480⟩, ⟨.hall 10 10, 278466300⟩, ⟨.hall 17 10, 122522400⟩, ⟨.hall 10 11, 413216100⟩, ⟨.hall 16 11, 515314800⟩, ⟨.hall 9 12, 235479420⟩, ⟨.hall 15 12, 5440535100⟩, ⟨.hall 9 13, 1691465490⟩, ⟨.hall 8 15, 5798072280⟩, ⟨.hall 8 19, 8963444730240⟩, ⟨.hall 7 20, 48713007142800⟩, ⟨.hall 6 21, 69773168064600⟩, ⟨.hall 5 22, 90815869544400⟩, ⟨.hall 4 23, 103333940269560⟩, ⟨.hall 3 24, 91701878027760⟩, ⟨.assumptionRow 18, 6680612400⟩]
  caps := #[0, 0, 0, 0, 0, 41031927090, 0, 4073869800, 1337040705, 1416154740, 0, 0, 575975400, 0, 0, 0, 41672400, 565950000, 70316400, 0, 0, 1745944200, 0, 147241294200, 0, 0, 0, 0, 0] }

theorem case_56_28_18_checked :
    (Witness.linear .conditional case_56_28_18).check 56 28 18 = true := by
  change case_56_28_18.check 56 28 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_29_1_checked :
    (Witness.rising).check 56 29 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_29_2_checked :
    (Witness.rising).check 56 29 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_29_3_checked :
    (Witness.rising).check 56 29 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_29_4_checked :
    (Witness.rising).check 56 29 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_29_5_checked :
    (Witness.rising).check 56 29 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_29_6_checked :
    (Witness.rising).check 56 29 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_29_7_checked :
    (Witness.rising).check 56 29 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_29_8_checked :
    (Witness.rising).check 56 29 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_29_9_checked :
    (Witness.rising).check 56 29 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_29_10_checked :
    (Witness.rising).check 56 29 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_29_11 : Certificate := {
  objectiveScale := 139514691690000000
  eta := 173640677493468289104000
  rows := #[⟨.count 2, 39479908974008446944000⟩, ⟨.count 3, 6560284275621164088000⟩, ⟨.count 4, 775413781046393448960⟩, ⟨.count 5, 105612097034089245600⟩, ⟨.count 6, 16188715603765504800⟩, ⟨.count 7, 2885001987106839600⟩, ⟨.count 8, 616712975381543040⟩, ⟨.count 9, 192538381070075040⟩, ⟨.count 10, 138932548281727200⟩, ⟨.count 12, 15513290789396400⟩, ⟨.path 11, 53805086951616000⟩, ⟨.path 12, 15582816461534400⟩, ⟨.privateRow 7 13, 61571181795397560⟩, ⟨.privateRow 7 14, 98261747520508000⟩, ⟨.privateRow 8 10, 47207353702659150⟩, ⟨.privateRow 8 11, 30846267105430140⟩, ⟨.privateRow 8 12, 50341532649516108⟩, ⟨.privateRow 9 5, 199792381378590⟩, ⟨.privateRow 9 6, 7016298603490176⟩, ⟨.privateRow 9 8, 34293357390710880⟩, ⟨.privateRow 9 9, 9856424148010440⟩, ⟨.privateRow 9 10, 6326293027148640⟩, ⟨.privateRow 10 3, 4932430917654240⟩, ⟨.privateRow 10 4, 3696159055503915⟩, ⟨.privateRow 11 0, 978264196509600⟩, ⟨.hall 7 9, 5393520965880⟩, ⟨.hall 6 11, 9902087637750⟩, ⟨.hall 5 17, 3871328725550⟩, ⟨.hall 5 18, 485560079604600⟩, ⟨.hall 8 20, 48500515379933760⟩, ⟨.hall 4 23, 689519368308530760⟩]
  caps := #[0, 0, 8332723887447960000, 0, 0, 189026943374926800, 10211035103309040, 0, 12091594089506106, 781397571540960, 582143408272800, 106516463824800, 69525672138000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_29_11_checked :
    (Witness.linear .positive case_56_29_11).check 56 29 11 = true := by
  change case_56_29_11.check 56 29 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_29_12 : Certificate := {
  objectiveScale := 119340000000
  eta := 250943337705060000
  rows := #[⟨.count 2, 62989825658760000⟩, ⟨.count 3, 11630766518411040⟩, ⟨.count 4, 1598451489835200⟩, ⟨.count 5, 241475722488000⟩, ⟨.count 6, 39594522567600⟩, ⟨.count 7, 7495920432000⟩, ⟨.count 8, 1584851748480⟩, ⟨.count 9, 410866616160⟩, ⟨.count 10, 152172820800⟩, ⟨.count 11, 118522404000⟩, ⟨.count 13, 18963584640⟩, ⟨.path 12, 31596458400⟩, ⟨.path 13, 18703666800⟩, ⟨.privateRow 8 11, 30421755000⟩, ⟨.privateRow 8 12, 84864527748⟩, ⟨.privateRow 8 13, 66630403840⟩, ⟨.privateRow 9 8, 13829951520⟩, ⟨.privateRow 9 9, 30293663400⟩, ⟨.privateRow 9 10, 45190716480⟩, ⟨.privateRow 9 11, 51682398768⟩, ⟨.privateRow 10 5, 5203934736⟩, ⟨.privateRow 10 6, 11191546080⟩, ⟨.privateRow 10 7, 16062686640⟩, ⟨.privateRow 10 8, 19937457540⟩, ⟨.privateRow 10 9, 4508824320⟩, ⟨.privateRow 11 3, 9199990800⟩, ⟨.privateRow 11 4, 508347840⟩, ⟨.privateRow 12 0, 1120644525⟩, ⟨.hall 8 9, 4833312⟩, ⟨.hall 7 10, 22973550⟩, ⟨.hall 8 10, 4763760⟩, ⟨.hall 6 13, 36040680⟩, ⟨.hall 6 14, 17330040⟩, ⟨.hall 9 19, 105506489088⟩, ⟨.hall 8 20, 4589339040⟩, ⟨.hall 5 22, 1766895530400⟩, ⟨.hall 4 24, 36845661460608⟩]
  caps := #[0, 0, 0, 970645206960, 95112388800, 36621468000, 26488130760, 19787367600, 3545680320, 0, 620446008, 817596000, 486666375, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_29_12_checked :
    (Witness.linear .positive case_56_29_12).check 56 29 12 = true := by
  change case_56_29_12.check 56 29 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_29_13 : Certificate := {
  objectiveScale := 7880683200000000
  eta := 24652004313911214240000
  rows := #[⟨.count 2, 6776654055835023360000⟩, ⟨.count 3, 1388444007121653081600⟩, ⟨.count 4, 213888143637292924800⟩, ⟨.count 5, 36704086011408816000⟩, ⟨.count 6, 6677274898934640000⟩, ⟨.count 7, 1316431404576288000⟩, ⟨.count 8, 287636457184876800⟩, ⟨.count 9, 72089337640320000⟩, ⟨.count 10, 21626801292096000⟩, ⟨.count 11, 8810919044928000⟩, ⟨.count 12, 7968698842104000⟩, ⟨.path 13, 1040629301712000⟩, ⟨.path 14, 1695238100556000⟩, ⟨.privateRow 8 13, 12703520779549600⟩, ⟨.privateRow 8 14, 21829552554209400⟩, ⟨.privateRow 9 10, 3284069825836800⟩, ⟨.privateRow 9 11, 6960626045493120⟩, ⟨.privateRow 9 12, 11142697620454400⟩, ⟨.privateRow 10 7, 810234863222400⟩, ⟨.privateRow 10 8, 2166017598544800⟩, ⟨.privateRow 10 9, 3557135498716800⟩, ⟨.privateRow 10 10, 4805955842688000⟩, ⟨.privateRow 10 11, 5780496888566400⟩, ⟨.privateRow 11 4, 160198528089600⟩, ⟨.privateRow 11 5, 738730607472000⟩, ⟨.privateRow 11 6, 1172493751968000⟩, ⟨.privateRow 11 7, 1637323191504000⟩, ⟨.privateRow 11 8, 1192922194464000⟩, ⟨.privateRow 12 2, 306722020980375⟩, ⟨.privateRow 12 3, 450263877663600⟩, ⟨.privateRow 12 4, 231379176600000⟩, ⟨.privateRow 13 0, 210364503148800⟩, ⟨.privateRow 14 0, 106029507676950⟩, ⟨.privateRow 15 0, 105385502302080⟩, ⟨.privateRow 16 0, 133043026545000⟩, ⟨.privateRow 17 0, 96046628832000⟩, ⟨.privateRow 18 0, 150186120084000⟩, ⟨.privateRow 19 0, 269424797241600⟩, ⟨.privateRow 20 0, 551683681108560⟩, ⟨.privateRow 21 0, 1328630649632000⟩, ⟨.privateRow 22 0, 3566920351995000⟩, ⟨.privateRow 23 0, 9566140677350400⟩, ⟨.privateRow 24 2, 12032411320729800⟩, ⟨.privateRow 25 4, 6930668920740364800⟩, ⟨.privateRow 27 2, 125137077735589920000⟩, ⟨.hall 24 2, 38503716226335360⟩, ⟨.hall 25 3, 2406482264145960000⟩, ⟨.hall 23 4, 6417286037722560⟩, ⟨.hall 23 5, 866333615092545600⟩, ⟨.hall 22 6, 185343975623664000⟩, ⟨.hall 21 7, 49936884927930000⟩, ⟨.hall 20 8, 16487098515888000⟩, ⟨.hall 8 9, 1857505557600⟩, ⟨.hall 19 9, 6391921270775040⟩, ⟨.hall 8 10, 1461920222400⟩, ⟨.hall 18 10, 3014645028595200⟩, ⟨.hall 7 11, 416766900000⟩, ⟨.hall 17 11, 1668734667600000⟩, ⟨.hall 7 12, 5346579981600⟩, ⟨.hall 9 12, 1100196488160⟩, ⟨.hall 16 12, 1076447123136000⟩, ⟨.hall 9 13, 1094678133120⟩, ⟨.hall 14 14, 11229602704320⟩, ⟨.hall 6 16, 39215569536000⟩, ⟨.hall 6 17, 43796040288000⟩, ⟨.hall 10 18, 8094241419264000⟩, ⟨.hall 5 23, 6164431017214470000⟩, ⟨.hall 4 24, 4920774933725659008⟩]
  caps := #[0, 0, 0, 271795007282198400, 0, 43678787508744960, 3619420478388000, 1281264031684000, 297120416156200, 0, 696908596154400, 113869130325600, 0, 68184272145600, 41628970189950, 0, 0, 57990417408000, 0, 0, 4394445873657840, 1781572916552000, 0, 0, 67381503396086880, 0, 62568538867794960000, 0] }

theorem case_56_29_13_checked :
    (Witness.linear .positive case_56_29_13).check 56 29 13 = true := by
  change case_56_29_13.check 56 29 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_29_14 : Certificate := {
  objectiveScale := 270415600000000
  eta := 1185958213994113560000
  rows := #[⟨.count 2, 365566533035263560000⟩, ⟨.count 3, 89074847151788097600⟩, ⟨.count 4, 15475868669607746400⟩, ⟨.count 5, 2839268600188020000⟩, ⟨.count 6, 552548389072680000⟩, ⟨.count 7, 114660276042312000⟩, ⟨.count 8, 25318649189433600⟩, ⟨.count 9, 6438888566510400⟩, ⟨.count 10, 1802233441008000⟩, ⟨.count 11, 618413435640000⟩, ⟨.count 12, 265034329560000⟩, ⟨.count 13, 275635702742400⟩, ⟨.path 15, 76825883206800⟩, ⟨.privateRow 8 14, 337236106006800⟩, ⟨.privateRow 9 11, 7645838840640⟩, ⟨.privateRow 9 12, 485450085120000⟩, ⟨.privateRow 9 13, 771410525886000⟩, ⟨.privateRow 10 9, 92842328779200⟩, ⟨.privateRow 10 10, 208349108407440⟩, ⟨.privateRow 10 11, 405350821075200⟩, ⟨.privateRow 10 12, 53589138302700⟩, ⟨.privateRow 11 6, 11738117160000⟩, ⟨.privateRow 11 7, 63715323672000⟩, ⟨.privateRow 11 8, 115067246112000⟩, ⟨.privateRow 11 9, 164160657460800⟩, ⟨.privateRow 11 10, 262000266528000⟩, ⟨.privateRow 12 4, 16801283391750⟩, ⟨.privateRow 12 5, 34998123006000⟩, ⟨.privateRow 12 6, 58620440253375⟩, ⟨.privateRow 12 7, 69270336135000⟩, ⟨.privateRow 13 2, 16255438879680⟩, ⟨.privateRow 13 3, 19625161069800⟩, ⟨.privateRow 14 0, 8921244843225⟩, ⟨.privateRow 15 0, 5123997038160⟩, ⟨.privateRow 16 0, 5206031473500⟩, ⟨.privateRow 17 0, 8154902448000⟩, ⟨.privateRow 17 9, 401567166000⟩, ⟨.privateRow 18 0, 4778649275400⟩, ⟨.privateRow 18 4, 3413320911000⟩, ⟨.privateRow 19 0, 5461313457600⟩, ⟨.privateRow 19 1, 7645838840640⟩, ⟨.privateRow 19 4, 2340562910400⟩, ⟨.privateRow 20 0, 29832424762140⟩, ⟨.privateRow 21 0, 74117825496000⟩, ⟨.privateRow 22 0, 210772566254250⟩, ⟨.privateRow 23 0, 733766472410400⟩, ⟨.privateRow 24 0, 2187711149223600⟩, ⟨.privateRow 26 3, 2953410051451860000⟩, ⟨.hall 15 3, 26476956000⟩, ⟨.hall 24 4, 236272804116148800⟩, ⟨.hall 23 5, 35003378387577600⟩, ⟨.hall 22 6, 7745312764332000⟩, ⟨.hall 17 7, 227554727400⟩, ⟨.hall 21 7, 2042872565233500⟩, ⟨.hall 20 8, 662942772492000⟩, ⟨.hall 9 9, 222060583080⟩, ⟨.hall 16 9, 18533869200⟩, ⟨.hall 19 9, 259412389236000⟩, ⟨.hall 8 10, 39260779200⟩, ⟨.hall 18 10, 120645379108800⟩, ⟨.hall 8 11, 316076016960⟩, ⟨.hall 10 12, 163584234000⟩, ⟨.hall 15 12, 145623258000⟩, ⟨.hall 7 13, 224251794000⟩, ⟨.hall 10 13, 11406252000⟩, ⟨.hall 7 14, 882940735950⟩, ⟨.hall 12 16, 44432225838000⟩, ⟨.hall 11 17, 369084844128000⟩, ⟨.hall 6 20, 188517077892000⟩, ⟨.hall 6 22, 217500370175088000⟩, ⟨.hall 5 23, 323044086545680500⟩, ⟨.hall 4 24, 180617432479900416⟩]
  caps := #[0, 0, 213347037692880000, 0, 11872702380084000, 23233567520800, 353089085349000, 89660759916000, 113460166201200, 18416385836640, 10799858232800, 0, 11438578951375, 0, 0, 2792960483040, 509681403000, 0, 0, 61095784576320, 47991292008660, 12352970916000, 2286071680142250, 0, 76569890222826000, 0, 0, 0] }

theorem case_56_29_14_checked :
    (Witness.linear .positive case_56_29_14).check 56 29 14 = true := by
  change case_56_29_14.check 56 29 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_29_15 : Certificate := {
  objectiveScale := 55773217500000
  eta := 304310620857002760000
  rows := #[⟨.count 2, 100415941749363240000⟩, ⟨.count 3, 25228684972846555200⟩, ⟨.count 4, 5066739021601857600⟩, ⟨.count 5, 1044394279064136000⟩, ⟨.count 6, 239437635264828000⟩, ⟨.count 7, 54908955721620000⟩, ⟨.count 8, 13800739107355200⟩, ⟨.count 9, 3506163239779200⟩, ⟨.count 10, 1037649556944000⟩, ⟨.count 11, 329820499008000⟩, ⟨.count 12, 119265448302000⟩, ⟨.count 13, 57424104738000⟩, ⟨.count 14, 57424104738000⟩, ⟨.path 16, 7647028669280⟩, ⟨.path 17, 5531447972160⟩, ⟨.privateRow 9 13, 190918416288600⟩, ⟨.privateRow 9 14, 470453144990400⟩, ⟨.privateRow 9 15, 74637950587200⟩, ⟨.privateRow 10 10, 3094744292640⟩, ⟨.privateRow 10 11, 102854736784800⟩, ⟨.privateRow 10 12, 241321788407700⟩, ⟨.privateRow 11 8, 11730628728000⟩, ⟨.privateRow 11 9, 43048000195200⟩, ⟨.privateRow 11 10, 112200840752000⟩, ⟨.privateRow 11 11, 101061070110000⟩, ⟨.privateRow 12 6, 8926503460875⟩, ⟨.privateRow 12 7, 23223967767000⟩, ⟨.privateRow 12 8, 46933162526250⟩, ⟨.privateRow 12 9, 82373324033000⟩, ⟨.privateRow 13 4, 5617821686400⟩, ⟨.privateRow 13 5, 12564590438400⟩, ⟨.privateRow 13 6, 23130268761600⟩, ⟨.privateRow 13 7, 32599222535880⟩, ⟨.privateRow 14 3, 14597922596400⟩, ⟨.privateRow 14 4, 1595114020500⟩, ⟨.privateRow 15 0, 3160779782160⟩, ⟨.privateRow 16 0, 683620294500⟩, ⟨.privateRow 17 0, 411863760000⟩, ⟨.privateRow 18 0, 151703151600⟩, ⟨.privateRow 19 0, 330988694400⟩, ⟨.privateRow 20 0, 864707964120⟩, ⟨.privateRow 21 0, 1372552324000⟩, ⟨.privateRow 23 6, 570707256319200⟩, ⟨.hall 21 7, 129706194618000⟩, ⟨.hall 20 8, 48039331340000⟩, ⟨.hall 10 9, 138930120000⟩, ⟨.hall 11 9, 59383755200⟩, ⟨.hall 19 9, 17294159282400⟩, ⟨.hall 9 10, 166583125800⟩, ⟨.hall 11 10, 11154643500⟩, ⟨.hall 17 10, 482691846000⟩, ⟨.hall 18 10, 7447245624000⟩, ⟨.hall 9 11, 55504060920⟩, ⟨.hall 8 13, 560621758840⟩, ⟨.hall 13 15, 27515716853625⟩, ⟨.hall 7 16, 4435781610000⟩, ⟨.hall 12 16, 176169877884000⟩, ⟨.hall 6 22, 141266964138300000⟩, ⟨.hall 5 23, 167724521440476000⟩, ⟨.hall 4 24, 113060912191875648⟩]
  caps := #[0, 1124881296364425600, 0, 0, 0, 30196151128000, 83780593856960, 0, 1518306332400, 8755439035200, 1548223556640, 4830721357280, 0, 0, 0, 2570624776720, 0, 3019079036160, 1779064232400, 37401722467200, 16429451318280, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_29_15_checked :
    (Witness.linear .positive case_56_29_15).check 56 29 15 = true := by
  change case_56_29_15.check 56 29 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_29_16 : Certificate := {
  objectiveScale := 67632364800000
  eta := 426603674098602000000
  rows := #[⟨.count 2, 131262668953416000000⟩, ⟨.count 3, 30662959467517977600⟩, ⟨.count 4, 6974423143724836800⟩, ⟨.count 5, 1774899567152712000⟩, ⟨.count 6, 452934031606056000⟩, ⟨.count 7, 116216750377728000⟩, ⟨.count 8, 32443842813782400⟩, ⟨.count 9, 9699292700697600⟩, ⟨.count 10, 3076539914448000⟩, ⟨.count 11, 1048358014704000⟩, ⟨.count 12, 406385971992000⟩, ⟨.count 13, 183757135161600⟩, ⟨.count 14, 168444040564800⟩, ⟨.count 15, 61841343564000⟩, ⟨.path 16, 15562958611200⟩, ⟨.privateRow 4 25, 315030405488198400⟩, ⟨.privateRow 9 13, 109681378606800⟩, ⟨.privateRow 10 11, 91021890960000⟩, ⟨.privateRow 10 12, 496069305732000⟩, ⟨.privateRow 10 13, 686044995292800⟩, ⟨.privateRow 11 9, 48830567385600⟩, ⟨.privateRow 11 10, 215596949568000⟩, ⟨.privateRow 11 11, 469298161332000⟩, ⟨.privateRow 12 7, 24830236431000⟩, ⟨.privateRow 12 8, 99093390996600⟩, ⟨.privateRow 12 9, 211454858615000⟩, ⟨.privateRow 12 10, 107210067339375⟩, ⟨.privateRow 13 5, 12171946987200⟩, ⟨.privateRow 13 6, 47545552454400⟩, ⟨.privateRow 13 7, 99829597467600⟩, ⟨.privateRow 13 8, 162227185920800⟩, ⟨.privateRow 13 9, 51608073617100⟩, ⟨.privateRow 14 3, 6310341180000⟩, ⟨.privateRow 14 4, 24109009052700⟩, ⟨.privateRow 14 5, 48773200647600⟩, ⟨.privateRow 14 6, 35438876066880⟩, ⟨.privateRow 15 0, 4004963202240⟩, ⟨.privateRow 15 2, 14271079284000⟩, ⟨.privateRow 15 3, 8343673338000⟩, ⟨.privateRow 16 0, 6941375298000⟩, ⟨.privateRow 17 0, 5189483376000⟩, ⟨.privateRow 18 0, 7585157580000⟩, ⟨.privateRow 18 5, 1300312728000⟩, ⟨.privateRow 19 0, 16549434720000⟩, ⟨.privateRow 20 0, 2594123892360⟩, ⟨.privateRow 20 2, 3242654865450⟩, ⟨.privateRow 20 4, 4323539820600⟩, ⟨.privateRow 21 0, 82353139440000⟩, ⟨.privateRow 21 3, 12352970916000⟩, ⟨.privateRow 21 4, 4941188366400⟩, ⟨.privateRow 21 6, 8235313944000⟩, ⟨.privateRow 22 0, 313456636993500⟩, ⟨.privateRow 23 0, 978355296547200⟩, ⟨.privateRow 23 1, 443883421581600⟩, ⟨.privateRow 24 0, 7656989022282600⟩, ⟨.privateRow 25 0, 59505743258881920⟩, ⟨.privateRow 26 1, 1166779279585920000⟩, ⟨.privateRow 27 0, 3792032658654240000⟩, ⟨.hall 19 1, 25076530959480⟩, ⟨.hall 22 3, 27176536015200⟩, ⟨.hall 24 4, 31503040548819840⟩, ⟨.hall 23 5, 5833896397929600⟩, ⟨.hall 19 6, 411765697200⟩, ⟨.hall 22 6, 1087061440608000⟩, ⟨.hall 21 7, 389118583854000⟩, ⟨.hall 11 8, 440505788800⟩, ⟨.hall 20 8, 115294395216000⟩, ⟨.hall 10 9, 546557004000⟩, ⟨.hall 19 9, 27670654851840⟩, ⟨.hall 10 10, 117187392000⟩, ⟨.hall 9 11, 1016306343360⟩, ⟨.hall 12 11, 218434887000⟩, ⟨.hall 12 12, 353778856200⟩, ⟨.hall 8 13, 2164340790040⟩, ⟨.hall 8 14, 138105110000⟩, ⟨.hall 14 14, 11229602704320⟩, ⟨.hall 13 15, 206248242850650⟩, ⟨.hall 7 17, 52523440080800⟩, ⟨.hall 6 22, 495861142624848000⟩, ⟨.hall 5 23, 647832000819003000⟩, ⟨.hall 4 24, 594007331237191872⟩, ⟨.assumptionRow 16, 119123263779520⟩]
  caps := #[0, 0, 25122041904960000, 25010388385382400, 0, 1156706190319680, 122578275659840, 102938283448000, 28796016412800, 19998809756640, 2089169116320, 0, 4735606625750, 2419986208640, 10159843877040, 0, 0, 5029073280000, 0, 90359913571200, 0, 0, 1826695574203500, 0, 0, 203019594647950080, 291694819896480000, 0] }

theorem case_56_29_16_checked :
    (Witness.linear .conditional case_56_29_16).check 56 29 16 = true := by
  change case_56_29_16.check 56 29 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_29_17 : Certificate := {
  objectiveScale := 72256800000000
  eta := 125137077735589920000
  rows := #[⟨.count 2, 33690751698043440000⟩, ⟨.count 3, 9345902029483219200⟩, ⟨.count 4, 2651505912859003200⟩, ⟨.count 5, 776161868594112000⟩, ⟨.count 6, 233989975090872000⟩, ⟨.count 7, 73154293764552000⟩, ⟨.count 8, 23865939809712000⟩, ⟨.count 9, 8159202305654400⟩, ⟨.count 10, 2894496132528000⟩, ⟨.count 11, 1095475228848000⟩, ⟨.count 12, 441723882600000⟩, ⟨.count 13, 191413682460000⟩, ⟨.count 14, 99535114879200⟩, ⟨.count 15, 79510298868000⟩, ⟨.count 16, 70675821216000⟩, ⟨.path 15, 5954551512000⟩, ⟨.privateRow 3 26, 1032599662433539200⟩, ⟨.privateRow 10 12, 353847601107000⟩, ⟨.privateRow 10 13, 824398269552000⟩, ⟨.privateRow 11 10, 114699480896000⟩, ⟨.privateRow 11 11, 458857415016000⟩, ⟨.privateRow 11 12, 383209809840000⟩, ⟨.privateRow 12 8, 36957564844200⟩, ⟨.privateRow 12 9, 174153730751000⟩, ⟨.privateRow 12 10, 395434900735875⟩, ⟨.privateRow 13 6, 12207641846400⟩, ⟨.privateRow 13 7, 71735958534240⟩, ⟨.privateRow 13 8, 176558671889600⟩, ⟨.privateRow 13 9, 313034991469200⟩, ⟨.privateRow 14 4, 2962354609500⟩, ⟨.privateRow 14 5, 30278164316400⟩, ⟨.privateRow 14 6, 78698368302840⟩, ⟨.privateRow 14 7, 146325126147200⟩, ⟨.privateRow 14 8, 122641480833300⟩, ⟨.privateRow 15 3, 13398957772200⟩, ⟨.privateRow 15 4, 37479602160000⟩, ⟨.privateRow 15 5, 52300107699840⟩, ⟨.privateRow 16 1, 6002914302000⟩, ⟨.privateRow 16 2, 19693523099250⟩, ⟨.privateRow 16 3, 401567166000⟩, ⟨.privateRow 17 0, 7001683920000⟩, ⟨.privateRow 18 0, 6068126064000⟩, ⟨.privateRow 19 0, 4302853027200⟩, ⟨.privateRow 20 0, 10376495569440⟩, ⟨.privateRow 21 0, 32941255776000⟩, ⟨.privateRow 22 0, 97279645963500⟩, ⟨.privateRow 24 3, 1458474099482400⟩, ⟨.privateRow 24 4, 5469277873059000⟩, ⟨.privateRow 24 5, 10938555746118000⟩, ⟨.hall 19 2, 576471976080⟩, ⟨.hall 18 4, 297889824960⟩, ⟨.hall 19 4, 713727208480⟩, ⟨.hall 22 4, 308000741505600⟩, ⟨.hall 19 6, 164706278880⟩, ⟨.hall 21 7, 713384070399000⟩, ⟨.hall 11 8, 430303412000⟩, ⟨.hall 12 8, 215945822400⟩, ⟨.hall 20 8, 230588790432000⟩, ⟨.hall 11 9, 620191448800⟩, ⟨.hall 12 9, 389165827050⟩, ⟨.hall 10 10, 1431013080000⟩, ⟨.hall 9 11, 293203643040⟩, ⟨.hall 9 12, 2274463422000⟩, ⟨.hall 8 14, 5205585287760⟩, ⟨.hall 14 14, 177121460836320⟩, ⟨.hall 8 15, 4775887173200⟩, ⟨.hall 13 15, 912564731128050⟩, ⟨.hall 12 16, 68597120592000⟩, ⟨.hall 7 17, 80779629694400⟩, ⟨.hall 6 22, 775417467825000000⟩, ⟨.hall 5 23, 1122232407634338000⟩, ⟨.hall 4 24, 1414486520642010816⟩, ⟨.hall 3 25, 1393403716582416000⟩, ⟨.assumptionRow 17, 75635978850432⟩]
  caps := #[0, 0, 0, 0, 0, 0, 34923023623488, 97875179770368, 61608028984320, 0, 17976350623608, 1443588509584, 0, 0, 1303994548220, 2080231494432, 10656870559566, 12018745229568, 0, 64873784102400, 0, 0, 1567283184967500, 0, 0, 0, 0, 0] }

theorem case_56_29_17_checked :
    (Witness.linear .conditional case_56_29_17).check 56 29 17 = true := by
  change case_56_29_17.check 56 29 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_29_18 : Certificate := {
  objectiveScale := 296111200000000
  eta := 238898057495217120000
  rows := #[⟨.count 2, 73507094613912960000⟩, ⟨.count 3, 22209643586917987200⟩, ⟨.count 4, 6799406251786948800⟩, ⟨.count 5, 2271414880150416000⟩, ⟨.count 6, 764228898689256000⟩, ⟨.count 7, 258374739679056000⟩, ⟨.count 8, 87785152517462400⟩, ⟨.count 9, 29982610882224000⟩, ⟨.count 10, 11031853184352000⟩, ⟨.count 11, 4558590468432000⟩, ⟨.count 12, 1828736873964000⟩, ⟨.count 13, 735028540646400⟩, ⟨.count 14, 413453554113600⟩, ⟨.count 15, 238530896604000⟩, ⟨.count 16, 212027463648000⟩, ⟨.count 17, 218452538304000⟩, ⟨.count 19, 207529911388800⟩, ⟨.path 15, 19911241459200⟩, ⟨.privateRow 2 27, 2625253379068320000⟩, ⟨.privateRow 10 12, 200703269566800⟩, ⟨.privateRow 11 11, 908746496658000⟩, ⟨.privateRow 11 12, 1843996426272000⟩, ⟨.privateRow 12 9, 207119420508000⟩, ⟨.privateRow 12 10, 1066487099052375⟩, ⟨.privateRow 13 7, 51416659934640⟩, ⟨.privateRow 13 8, 374385530719200⟩, ⟨.privateRow 13 9, 1007351314269300⟩, ⟨.privateRow 14 5, 3281377413600⟩, ⟨.privateRow 14 6, 140607022172760⟩, ⟨.privateRow 14 7, 426761362513200⟩, ⟨.privateRow 14 8, 874692166812750⟩, ⟨.privateRow 15 4, 37586686737600⟩, ⟨.privateRow 15 5, 186230788904160⟩, ⟨.privateRow 15 6, 408741832699200⟩, ⟨.privateRow 15 7, 532939864356900⟩, ⟨.privateRow 16 2, 7362064710000⟩, ⟨.privateRow 16 3, 76498545123000⟩, ⟨.privateRow 16 4, 199217471052600⟩, ⟨.privateRow 16 5, 49816637871000⟩, ⟨.privateRow 17 1, 35070199164000⟩, ⟨.privateRow 17 2, 50232401856000⟩, ⟨.privateRow 18 0, 13653283644000⟩, ⟨.hall 13 7, 782163602220⟩, ⟨.hall 12 8, 5088455618400⟩, ⟨.hall 13 8, 2675998975650⟩, ⟨.hall 11 9, 5982442250400⟩, ⟨.hall 12 9, 651819826350⟩, ⟨.hall 10 10, 34223448000⟩, ⟨.hall 11 10, 1639884015000⟩, ⟨.hall 10 11, 11372046147000⟩, ⟨.hall 9 12, 1522996314840⟩, ⟨.hall 9 13, 23671750382280⟩, ⟨.hall 15 13, 603899650926000⟩, ⟨.hall 14 14, 2906425354472640⟩, ⟨.hall 8 15, 72192215323800⟩, ⟨.hall 13 15, 534044174063400⟩, ⟨.hall 8 19, 7343100031307040⟩, ⟨.hall 7 21, 2074473710831340000⟩, ⟨.hall 6 22, 3159913592083248000⟩, ⟨.hall 5 23, 4431541845318588000⟩, ⟨.hall 4 24, 5598090305525285568⟩, ⟨.hall 3 25, 6094626690790915200⟩, ⟨.hall 2 26, 5007427741556240000⟩, ⟨.assumptionRow 18, 207882813600000⟩]
  caps := #[0, 15331546395721920000, 175661335040800000, 120849510436928000, 0, 1971936137223360, 1117120957568000, 85041804848000, 18090184112000, 45181656540800, 0, 2870176946000, 1848767508000, 3147369449770, 11010101897730, 2295752007640, 0, 0, 36225741244000, 88581288611200, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_29_18_checked :
    (Witness.linear .conditional case_56_29_18).check 56 29 18 = true := by
  change case_56_29_18.check 56 29 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_30_1_checked :
    (Witness.rising).check 56 30 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_30_2_checked :
    (Witness.rising).check 56 30 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_30_3_checked :
    (Witness.rising).check 56 30 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_30_4_checked :
    (Witness.rising).check 56 30 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_30_5_checked :
    (Witness.rising).check 56 30 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_30_6_checked :
    (Witness.rising).check 56 30 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_30_7_checked :
    (Witness.rising).check 56 30 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_30_8_checked :
    (Witness.rising).check 56 30 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_30_9_checked :
    (Witness.rising).check 56 30 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_30_10_checked :
    (Witness.rising).check 56 30 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_30_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_30_11_checked :
    (Witness.linear .positive case_56_30_11).check 56 30 11 = true := by
  change case_56_30_11.check 56 30 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_30_12 : Certificate := {
  objectiveScale := 1126753200000000
  eta := 3252688936665648480000
  rows := #[⟨.count 2, 755652932631025228800⟩, ⟨.count 3, 120643519035084645600⟩, ⟨.count 4, 16603015500838166400⟩, ⟨.count 5, 2480501265874632000⟩, ⟨.count 6, 408833925435936000⟩, ⟨.count 7, 75177710400592800⟩, ⟨.count 8, 15750428011718400⟩, ⟨.count 9, 3975836197132800⟩, ⟨.count 10, 1439216722944000⟩, ⟨.count 11, 1113144184152000⟩, ⟨.path 12, 316765894339440⟩, ⟨.path 13, 167781886818000⟩, ⟨.privateRow 6 18, 2050593172056000⟩, ⟨.privateRow 6 19, 17957102054892000⟩, ⟨.privateRow 7 15, 2732477166619200⟩, ⟨.privateRow 7 16, 4662937696517100⟩, ⟨.privateRow 7 17, 6715074989937600⟩, ⟨.privateRow 7 18, 9702023357426400⟩, ⟨.privateRow 7 19, 3476126015762400⟩, ⟨.privateRow 8 11, 203889035750400⟩, ⟨.privateRow 8 12, 858419178926400⟩, ⟨.privateRow 8 13, 1525344848707680⟩, ⟨.privateRow 8 14, 2174816381337600⟩, ⟨.privateRow 8 15, 2616310478281500⟩, ⟨.privateRow 8 16, 2883573505612800⟩, ⟨.privateRow 8 17, 3756018330464400⟩, ⟨.privateRow 9 9, 523445889859200⟩, ⟨.privateRow 9 10, 372380669460800⟩, ⟨.privateRow 9 11, 677313198307200⟩, ⟨.privateRow 9 12, 829148745384960⟩, ⟨.privateRow 9 13, 917500660876800⟩, ⟨.privateRow 9 14, 454502642193600⟩, ⟨.privateRow 10 5, 46381007673000⟩, ⟨.privateRow 10 6, 73160183416320⟩, ⟨.privateRow 10 7, 225520120425600⟩, ⟨.privateRow 10 8, 239754131971200⟩, ⟨.privateRow 10 9, 110190030350400⟩, ⟨.privateRow 11 3, 90612449928000⟩, ⟨.privateRow 11 4, 19501105498875⟩, ⟨.privateRow 12 0, 21047755528800⟩, ⟨.privateRow 13 0, 9325281966000⟩, ⟨.privateRow 14 0, 7795127340000⟩, ⟨.privateRow 15 0, 9276201534600⟩, ⟨.privateRow 16 0, 12743064734400⟩, ⟨.privateRow 17 0, 20238985166400⟩, ⟨.privateRow 17 12, 8995104518400⟩, ⟨.privateRow 18 0, 38555939452800⟩, ⟨.privateRow 18 12, 8495376489600⟩, ⟨.privateRow 19 0, 86015686957200⟩, ⟨.privateRow 20 0, 235829444760000⟩, ⟨.privateRow 21 0, 795531326990400⟩, ⟨.privateRow 22 0, 3308949142699200⟩, ⟨.privateRow 23 0, 18476647423334100⟩, ⟨.privateRow 24 0, 144388935848757600⟩, ⟨.privateRow 25 0, 1715165540991302400⟩, ⟨.privateRow 26 4, 220521283841738880000⟩, ⟨.hall 13 10, 1349805600⟩, ⟨.hall 18 11, 12743064734400⟩, ⟨.hall 15 12, 67957520400⟩, ⟨.hall 14 13, 58896517680⟩, ⟨.hall 6 17, 1305024006000⟩, ⟨.hall 5 20, 22926723412320⟩, ⟨.hall 5 21, 106010462146680⟩, ⟨.hall 7 22, 16042964454316800⟩, ⟨.hall 4 24, 25543100770520256⟩]
  caps := #[0, 21109093600467600, 144671931182469600, 21921170421836400, 6407649894122400, 1308926965750560, 1629952340367120, 116716570585560, 49829770728000, 30921122367000, 4882428710280, 37576029814110, 0, 4049567667600, 0, 6184134356400, 47224298721600, 0, 35288486956800, 0, 330161222664000, 0, 5568719288932800, 38950770243785400, 0, 4410425676834777600, 0] }

theorem case_56_30_12_checked :
    (Witness.linear .positive case_56_30_12).check 56 30 12 = true := by
  change case_56_30_12.check 56 30 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_30_13 : Certificate := {
  objectiveScale := 852087600000000
  eta := 3862024063070453280000
  rows := #[⟨.count 2, 983060670599751744000⟩, ⟨.count 3, 174269846151774172800⟩, ⟨.count 4, 27310324671658828800⟩, ⟨.count 5, 4503781369078992000⟩, ⟨.count 6, 814609515335616000⟩, ⟨.count 7, 158326207792552800⟩, ⟨.count 8, 33995813960908800⟩, ⟨.count 9, 8233361193657600⟩, ⟨.count 10, 2421576821664000⟩, ⟨.count 11, 966677844132000⟩, ⟨.count 12, 859269194784000⟩, ⟨.path 13, 132648263748000⟩, ⟨.path 14, 172585052640000⟩, ⟨.privateRow 6 19, 4205211362352000⟩, ⟨.privateRow 7 16, 3244020193814400⟩, ⟨.privateRow 7 17, 10633177301947200⟩, ⟨.privateRow 7 18, 14913481724341200⟩, ⟨.privateRow 7 19, 16075922293791360⟩, ⟨.privateRow 8 13, 1078968704814000⟩, ⟨.privateRow 8 14, 2899382570884800⟩, ⟨.privateRow 8 15, 4635415551066300⟩, ⟨.privateRow 8 16, 6796317160432800⟩, ⟨.privateRow 8 17, 8803277996713200⟩, ⟨.privateRow 8 18, 7576020259647840⟩, ⟨.privateRow 9 10, 296332145709600⟩, ⟨.privateRow 9 11, 832994021059200⟩, ⟨.privateRow 9 12, 1389933018714240⟩, ⟨.privateRow 9 13, 1985384389788800⟩, ⟨.privateRow 9 14, 2429062879042800⟩, ⟨.privateRow 9 15, 3288285576576000⟩, ⟨.privateRow 9 16, 3076444101931200⟩, ⟨.privateRow 10 7, 73093678257600⟩, ⟨.privateRow 10 8, 252372770496000⟩, ⟨.privateRow 10 9, 432238443436800⟩, ⟨.privateRow 10 10, 627763610073600⟩, ⟨.privateRow 10 11, 792089966828160⟩, ⟨.privateRow 10 12, 918289705132800⟩, ⟨.privateRow 10 13, 120102398816400⟩, ⟨.privateRow 11 4, 13731219376875⟩, ⟨.privateRow 11 5, 84950477211600⟩, ⟨.privateRow 11 6, 145071422496000⟩, ⟨.privateRow 11 7, 214441743978000⟩, ⟨.privateRow 11 8, 156637613632500⟩, ⟨.privateRow 12 2, 33065015583600⟩, ⟨.privateRow 12 3, 56837076946650⟩, ⟨.privateRow 12 4, 10979550822240⟩, ⟨.privateRow 13 0, 20117810512800⟩, ⟨.privateRow 14 0, 10109049350400⟩, ⟨.privateRow 15 0, 10069560876375⟩, ⟨.privateRow 16 0, 14646634002000⟩, ⟨.privateRow 17 0, 23434614403200⟩, ⟨.privateRow 18 0, 43130372947200⟩, ⟨.privateRow 19 0, 99597111213600⟩, ⟨.privateRow 20 0, 270335016151200⟩, ⟨.privateRow 21 0, 901116720504000⟩, ⟨.privateRow 22 0, 3784690226116800⟩, ⟨.privateRow 23 0, 20815796243642400⟩, ⟨.privateRow 24 0, 159587771201258400⟩, ⟨.privateRow 25 0, 1915053254415100800⟩, ⟨.privateRow 26 0, 47876331360377520000⟩, ⟨.hall 14 4, 7868765520⟩, ⟨.hall 17 5, 12897838800⟩, ⟨.hall 7 15, 195706561050⟩, ⟨.hall 6 16, 959656698000⟩, ⟨.hall 7 16, 720799279200⟩, ⟨.hall 6 17, 1368006354000⟩, ⟨.hall 5 21, 378344362195800⟩, ⟨.hall 8 21, 6603590282889600⟩, ⟨.hall 5 22, 873038445879600⟩, ⟨.hall 4 24, 42015884110244352⟩]
  caps := #[0, 0, 0, 69091986771007200, 10214476603531200, 136882920636000, 0, 0, 211105943160840, 33614142962400, 82521453324240, 18058019616000, 0, 0, 3258476020800, 22130903025000, 0, 0, 31212769896000, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_30_13_checked :
    (Witness.linear .positive case_56_30_13).check 56 30 13 = true := by
  change case_56_30_13.check 56 30 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_30_14 : Certificate := {
  objectiveScale := 151103534400000
  eta := 937215456327390240000
  rows := #[⟨.count 2, 260656157500935356160⟩, ⟨.count 3, 50885286246481246560⟩, ⟨.count 4, 8955081700355831040⟩, ⟨.count 5, 1656088692882624000⟩, ⟨.count 6, 323124072032361600⟩, ⟨.count 7, 66897266936179680⟩, ⟨.count 8, 14863510706204160⟩, ⟨.count 9, 3761752709594880⟩, ⟨.count 10, 1025441915097600⟩, ⟨.count 11, 352495658314800⟩, ⟨.count 12, 148419224553600⟩, ⟨.count 13, 151599636508320⟩, ⟨.path 14, 2386335369600⟩, ⟨.path 15, 41135270707440⟩, ⟨.privateRow 6 20, 3839303360692800⟩, ⟨.privateRow 7 17, 1107320312910240⟩, ⟨.privateRow 7 18, 5250506758136640⟩, ⟨.privateRow 7 19, 8604190126179648⟩, ⟨.privateRow 8 14, 152916776812800⟩, ⟨.privateRow 8 15, 1264430598270840⟩, ⟨.privateRow 8 16, 2088952397532000⟩, ⟨.privateRow 8 17, 3952898680610880⟩, ⟨.privateRow 8 18, 4640259592384416⟩, ⟨.privateRow 9 12, 293600211480576⟩, ⟨.privateRow 9 13, 545969529064960⟩, ⟨.privateRow 9 14, 986950363679280⟩, ⟨.privateRow 9 15, 1453437554849280⟩, ⟨.privateRow 9 16, 1922503699596480⟩, ⟨.privateRow 9 17, 1910440264981248⟩, ⟨.privateRow 10 9, 50822340528960⟩, ⟨.privateRow 10 10, 144494088036480⟩, ⟨.privateRow 10 11, 277409023347456⟩, ⟨.privateRow 10 12, 348710218496640⟩, ⟨.privateRow 10 13, 668898459749520⟩, ⟨.privateRow 10 14, 644948993969280⟩, ⟨.privateRow 10 15, 621111966995520⟩, ⟨.privateRow 11 6, 5662097040600⟩, ⟨.privateRow 11 7, 40867181586000⟩, ⟨.privateRow 11 8, 76177291390200⟩, ⟨.privateRow 11 9, 121280585353200⟩, ⟨.privateRow 11 10, 172368690333840⟩, ⟨.privateRow 11 11, 211384956182400⟩, ⟨.privateRow 12 4, 9729704720736⟩, ⟨.privateRow 12 5, 23588055330840⟩, ⟨.privateRow 12 6, 41290989395040⟩, ⟨.privateRow 12 7, 50297626098720⟩, ⟨.privateRow 13 2, 10270080270450⟩, ⟨.privateRow 13 3, 11096103930912⟩, ⟨.privateRow 14 0, 4427632329120⟩, ⟨.privateRow 15 0, 2550955422015⟩, ⟨.privateRow 16 0, 3148286581440⟩, ⟨.privateRow 17 0, 5204310471360⟩, ⟨.privateRow 18 0, 9802357488000⟩, ⟨.privateRow 19 0, 21981786666840⟩, ⟨.privateRow 20 0, 59429020079520⟩, ⟨.privateRow 21 0, 197153415819360⟩, ⟨.privateRow 22 0, 823201981842240⟩, ⟨.privateRow 23 0, 4494319643513700⟩, ⟨.privateRow 24 0, 36753547306956480⟩, ⟨.privateRow 25 0, 441042567683477760⟩, ⟨.privateRow 26 4, 55130320960434720000⟩, ⟨.hall 20 6, 741178254960⟩, ⟨.hall 15 9, 617795640⟩, ⟨.hall 7 15, 364370618430⟩, ⟨.hall 8 15, 165084454080⟩, ⟨.hall 8 16, 156579171840⟩, ⟨.hall 6 18, 4221647726400⟩, ⟨.hall 6 19, 3755693766240⟩, ⟨.hall 5 24, 356407719220897344⟩, ⟨.hall 4 25, 344426219244455040⟩]
  caps := #[0, 2312977461494918400, 123533123071962240, 0, 1880346772886400, 713051490412800, 294692474172096, 233322914661408, 31505842440072, 28144848123392, 12682411691040, 10961154897840, 5070645216000, 692322957144, 3013299263520, 2639034338850, 8426732529600, 0, 0, 0, 506561647344480, 0, 0, 43744711196866680, 0, 0, 0] }

theorem case_56_30_14_checked :
    (Witness.linear .positive case_56_30_14).check 56 30 14 = true := by
  change case_56_30_14.check 56 30 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_30_15 : Certificate := {
  objectiveScale := 2614248000000
  eta := 20106352350276192000
  rows := #[⟨.count 2, 5694637859207256960⟩, ⟨.count 3, 1173951540451609920⟩, ⟨.count 4, 240825033760671360⟩, ⟨.count 5, 50054383480701600⟩, ⟨.count 6, 11554533007617600⟩, ⟨.count 7, 2634103919406960⟩, ⟨.count 8, 663838713457920⟩, ⟨.count 9, 167308944042240⟩, ⟨.count 10, 49208512953600⟩, ⟨.count 11, 15824108500200⟩, ⟨.count 12, 5674852703520⟩, ⟨.count 13, 2432079730080⟩, ⟨.count 14, 2619162786240⟩, ⟨.path 16, 395282140344⟩, ⟨.path 17, 218754533088⟩, ⟨.privateRow 4 26, 9517382774499600⟩, ⟨.privateRow 7 18, 120397867710120⟩, ⟨.privateRow 7 19, 336564685705248⟩, ⟨.privateRow 8 15, 5270569053750⟩, ⟨.privateRow 8 16, 67366907768160⟩, ⟨.privateRow 8 17, 151173975312360⟩, ⟨.privateRow 8 18, 245431426784544⟩, ⟨.privateRow 9 13, 9278283734720⟩, ⟨.privateRow 9 14, 26235721512000⟩, ⟨.privateRow 9 15, 63543988347840⟩, ⟨.privateRow 9 16, 98271516863520⟩, ⟨.privateRow 9 17, 124552213898112⟩, ⟨.privateRow 10 10, 28861297920⟩, ⟨.privateRow 10 11, 5825652985152⟩, ⟨.privateRow 10 12, 12504959026560⟩, ⟨.privateRow 10 13, 24336387555480⟩, ⟨.privateRow 10 14, 40183172789760⟩, ⟨.privateRow 10 15, 51549885747360⟩, ⟨.privateRow 10 16, 55732609348416⟩, ⟨.privateRow 11 8, 524990015550⟩, ⟨.privateRow 11 9, 2457719901000⟩, ⟨.privateRow 11 10, 5917918946940⟩, ⟨.privateRow 11 11, 10654128084600⟩, ⟨.privateRow 11 12, 15669091763325⟩, ⟨.privateRow 11 13, 21202746364800⟩, ⟨.privateRow 11 14, 22694450278500⟩, ⟨.privateRow 12 6, 458913137760⟩, ⟨.privateRow 12 7, 1267141255380⟩, ⟨.privateRow 12 8, 2480267790000⟩, ⟨.privateRow 12 9, 4936394306844⟩, ⟨.privateRow 12 10, 7045062864840⟩, ⟨.privateRow 12 11, 3801423766140⟩, ⟨.privateRow 13 4, 309577914360⟩, ⟨.privateRow 13 5, 714753214560⟩, ⟨.privateRow 13 6, 1213441489260⟩, ⟨.privateRow 13 7, 2148620554080⟩, ⟨.privateRow 13 8, 68597120592⟩, ⟨.privateRow 14 2, 218263565520⟩, ⟨.privateRow 14 3, 416482517880⟩, ⟨.privateRow 14 4, 206271061920⟩, ⟨.privateRow 15 0, 136414728450⟩, ⟨.privateRow 16 0, 26456189760⟩, ⟨.privateRow 17 0, 17007550560⟩, ⟨.privateRow 18 0, 34596555840⟩, ⟨.privateRow 19 0, 56219403240⟩, ⟨.privateRow 20 0, 166467843360⟩, ⟨.privateRow 21 0, 610382092320⟩, ⟨.privateRow 22 0, 2848449764160⟩, ⟨.privateRow 23 0, 17624782915740⟩, ⟨.privateRow 24 0, 77213334678480⟩, ⟨.privateRow 25 0, 1080986685498720⟩, ⟨.privateRow 26 0, 32429600564961600⟩, ⟨.hall 8 14, 7605627120⟩, ⟨.hall 8 15, 13582983960⟩, ⟨.hall 9 15, 19688809140⟩, ⟨.hall 7 16, 20394869040⟩, ⟨.hall 9 16, 5079057984⟩, ⟨.hall 7 17, 116142324480⟩, ⟨.hall 6 21, 40262901751800⟩, ⟨.hall 5 24, 17814489670033056⟩, ⟨.hall 4 25, 18069469746229440⟩]
  caps := #[0, 52050192739140960, 300150283043520, 360960694174080, 252793102096080, 0, 0, 10310638554216, 2978039562498, 0, 232936140528, 149468353398, 298908930348, 182168269920, 221107802760, 0, 0, 490875342048, 0, 1011949258320, 3162889023840, 12207641846400, 59817445047360, 0, 1775906697605040, 25943680451969280, 0] }

theorem case_56_30_15_checked :
    (Witness.linear .positive case_56_30_15).check 56 30 15 = true := by
  change case_56_30_15.check 56 30 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_30_16 : Certificate := {
  objectiveScale := 506338560000
  eta := 5999476104517896000
  rows := #[⟨.count 2, 1660395548926033920⟩, ⟨.count 3, 357266099557326960⟩, ⟨.count 4, 85256949891072960⟩, ⟨.count 5, 19953390597940800⟩, ⟨.count 6, 4925783485022400⟩, ⟨.count 7, 1286075068518240⟩, ⟨.count 8, 340014950795520⟩, ⟨.count 9, 93099331765440⟩, ⟨.count 10, 29101808736000⟩, ⟨.count 11, 9639974143800⟩, ⟨.count 12, 3637726092000⟩, ⟨.count 13, 1621386486720⟩, ⟨.count 14, 1018563305760⟩, ⟨.count 15, 909431523000⟩, ⟨.path 16, 140989008888⟩, ⟨.privateRow 4 26, 7331909692947840⟩, ⟨.privateRow 7 18, 20244339395280⟩, ⟨.privateRow 7 19, 157356503400096⟩, ⟨.privateRow 8 16, 16881883658640⟩, ⟨.privateRow 8 17, 61578986348880⟩, ⟨.privateRow 8 18, 133239985678800⟩, ⟨.privateRow 9 14, 8701514301480⟩, ⟨.privateRow 9 15, 25750271426880⟩, ⟨.privateRow 9 16, 50022775682880⟩, ⟨.privateRow 9 17, 76298475437184⟩, ⟨.privateRow 10 11, 100533521088⟩, ⟨.privateRow 10 12, 3830268361920⟩, ⟨.privateRow 10 13, 10830502683000⟩, ⟨.privateRow 10 14, 20318353735680⟩, ⟨.privateRow 10 15, 30640677107040⟩, ⟨.privateRow 10 16, 38176281823680⟩, ⟨.privateRow 11 9, 225478890000⟩, ⟨.privateRow 11 10, 1531151982360⟩, ⟨.privateRow 11 11, 4526948025600⟩, ⟨.privateRow 11 12, 8509385409525⟩, ⟨.privateRow 11 13, 12774560198400⟩, ⟨.privateRow 11 14, 16171345990800⟩, ⟨.privateRow 11 15, 16482206220480⟩, ⟨.privateRow 12 7, 158645276790⟩, ⟨.privateRow 12 8, 727545218400⟩, ⟨.privateRow 12 9, 1863728334468⟩, ⟨.privateRow 12 10, 3667366823120⟩, ⟨.privateRow 12 11, 5608161058500⟩, ⟨.privateRow 12 12, 7213091165280⟩, ⟨.privateRow 12 13, 521407406520⟩, ⟨.privateRow 13 5, 91143027360⟩, ⟨.privateRow 13 6, 364638734460⟩, ⟨.privateRow 13 7, 873999126000⟩, ⟨.privateRow 13 8, 1600599480480⟩, ⟨.privateRow 13 9, 2097177962880⟩, ⟨.privateRow 14 3, 52709908680⟩, ⟨.privateRow 14 4, 196677059040⟩, ⟨.privateRow 14 5, 443456133120⟩, ⟨.privateRow 14 6, 422354172240⟩, ⟨.privateRow 15 1, 34760493768⟩, ⟨.privateRow 15 2, 122989786920⟩, ⟨.privateRow 15 3, 52234015680⟩, ⟨.privateRow 16 0, 48503014560⟩, ⟨.privateRow 17 0, 35904828960⟩, ⟨.privateRow 18 0, 65349049920⟩, ⟨.privateRow 19 0, 140548508100⟩, ⟨.privateRow 20 0, 388424967840⟩, ⟨.privateRow 21 0, 1322494533360⟩, ⟨.privateRow 22 0, 5222157900960⟩, ⟨.privateRow 23 0, 29374638192900⟩, ⟨.privateRow 24 0, 231640004035440⟩, ⟨.privateRow 25 0, 2882631161329920⟩, ⟨.privateRow 26 0, 64859201129923200⟩, ⟨.hall 21 6, 84775290600⟩, ⟨.hall 9 14, 9952014072⟩, ⟨.hall 8 15, 19538489880⟩, ⟨.hall 8 16, 8619811200⟩, ⟨.hall 7 18, 350585595360⟩, ⟨.hall 7 19, 252234971352⟩, ⟨.hall 10 19, 43824678337440⟩, ⟨.hall 6 23, 5912313541734600⟩, ⟨.hall 5 24, 9546864229558656⟩, ⟨.hall 4 25, 10043414756907840⟩, ⟨.assumptionRow 16, 986926187520⟩]
  caps := #[0, 26582741741162880, 1957153672918080, 0, 46690725476304, 10070072839008, 0, 389703394080, 0, 479112484032, 293991690720, 50690245788, 0, 160531938000, 0, 67085527992, 0, 181305371520, 0, 393535822680, 1276253465760, 5086517436000, 0, 105748697494440, 1003773350820240, 0, 0] }

theorem case_56_30_16_checked :
    (Witness.linear .conditional case_56_30_16).check 56 30 16 = true := by
  change case_56_30_16.check 56 30 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_30_17 : Certificate := {
  objectiveScale := 42270228000000
  eta := 215927090428369320000
  rows := #[⟨.count 2, 55130320960434720000⟩, ⟨.count 3, 14150115713178244800⟩, ⟨.count 4, 3683344632284116800⟩, ⟨.count 5, 1031423659602336000⟩, ⟨.count 6, 294692474172096000⟩, ⟨.count 7, 86254619420970000⟩, ⟨.count 8, 26072310446582400⟩, ⟨.count 9, 8181047559484800⟩, ⟨.count 10, 2676043594224000⟩, ⟨.count 11, 927620153460000⟩, ⟨.count 12, 346311523958400⟩, ⟨.count 13, 137817851371200⟩, ⟨.count 14, 74209612276800⟩, ⟨.count 15, 61841343564000⟩, ⟨.count 16, 44975522592000⟩, ⟨.path 15, 5149001075400⟩, ⟨.privateRow 3 27, 980094594852172800⟩, ⟨.privateRow 6 20, 2818947963031200⟩, ⟨.privateRow 7 18, 1642945131828000⟩, ⟨.privateRow 7 19, 15102989301319920⟩, ⟨.privateRow 8 16, 722258704767600⟩, ⟨.privateRow 8 17, 5342529889897200⟩, ⟨.privateRow 8 18, 13569452482425840⟩, ⟨.privateRow 9 14, 284064151371000⟩, ⟨.privateRow 9 15, 1919955086649600⟩, ⟨.privateRow 9 16, 4901832234499200⟩, ⟨.privateRow 9 17, 8758733160777600⟩, ⟨.privateRow 10 12, 105192750062400⟩, ⟨.privateRow 10 13, 704429122597200⟩, ⟨.privateRow 10 14, 1840462635211200⟩, ⟨.privateRow 10 15, 3382908890961600⟩, ⟨.privateRow 10 16, 4845213048836160⟩, ⟨.privateRow 11 10, 37245354646500⟩, ⟨.privateRow 11 11, 264543525246000⟩, ⟨.privateRow 11 12, 716797391310000⟩, ⟨.privateRow 11 13, 1368540901728000⟩, ⟨.privateRow 11 14, 2080352167393500⟩, ⟨.privateRow 11 15, 2565010272825000⟩, ⟨.privateRow 12 8, 12368268712800⟩, ⟨.privateRow 12 9, 101935147974660⟩, ⟨.privateRow 12 10, 288249373612200⟩, ⟨.privateRow 12 11, 570099885980625⟩, ⟨.privateRow 12 12, 901116720504000⟩, ⟨.privateRow 12 13, 1180482536032800⟩, ⟨.privateRow 12 14, 950295312766800⟩, ⟨.privateRow 13 6, 3533791060800⟩, ⟨.privateRow 13 7, 40718910632400⟩, ⟨.privateRow 13 8, 120855654279360⟩, ⟨.privateRow 13 9, 248641465472400⟩, ⟨.privateRow 13 10, 410471917906050⟩, ⟨.privateRow 13 11, 434151473184000⟩, ⟨.privateRow 14 4, 407745122400⟩, ⟨.privateRow 14 5, 17153610774300⟩, ⟨.privateRow 14 6, 53569059944400⟩, ⟨.privateRow 14 7, 114583175146440⟩, ⟨.privateRow 14 8, 150382441809600⟩, ⟨.privateRow 15 3, 7056255868200⟩, ⟨.privateRow 15 4, 25595444975100⟩, ⟨.privateRow 15 5, 45912512646000⟩, ⟨.privateRow 16 1, 3814888077000⟩, ⟨.privateRow 16 2, 11784451833000⟩, ⟨.privateRow 17 0, 3694417927200⟩, ⟨.privateRow 18 0, 3267452496000⟩, ⟨.privateRow 19 0, 2389324637700⟩, ⟨.privateRow 19 1, 5213071936800⟩, ⟨.privateRow 20 0, 18866355580800⟩, ⟨.privateRow 21 0, 51882477847200⟩, ⟨.privateRow 21 2, 10808849551500⟩, ⟨.privateRow 22 0, 242118229953600⟩, ⟨.privateRow 23 0, 1498106547837900⟩, ⟨.privateRow 24 0, 10938555746118000⟩, ⟨.privateRow 25 0, 122511824356521600⟩, ⟨.privateRow 26 0, 3675354730695648000⟩, ⟨.hall 9 13, 69651942360⟩, ⟨.hall 10 13, 567912945600⟩, ⟨.hall 9 14, 1769431744080⟩, ⟨.hall 10 14, 508043936400⟩, ⟨.hall 8 16, 8976146961600⟩, ⟨.hall 11 18, 1467918207756000⟩, ⟨.hall 7 19, 75188579061960⟩, ⟨.hall 7 20, 1163493617176800⟩, ⟨.hall 6 23, 716086282786875000⟩, ⟨.hall 5 24, 1159116814079864640⟩, ⟨.hall 4 25, 1487350911084192000⟩, ⟨.hall 3 26, 1432707723724877600⟩, ⟨.assumptionRow 17, 50662236276288⟩]
  caps := #[0, 0, 0, 19126098958730400, 0, 0, 88006583954016, 109381006366632, 0, 100739047456320, 13097458974600, 5947977554064, 1277484036192, 24731974420920, 291635501976, 0, 5686713684288, 18711661917312, 21358532025600, 3040958629800, 0, 0, 5084482829025600, 0, 0, 2940283784556518400, 0] }

theorem case_56_30_17_checked :
    (Witness.linear .conditional case_56_30_17).check 56 30 17 = true := by
  change case_56_30_17.check 56 30 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_30_18 : Certificate := {
  objectiveScale := 680149008000000
  eta := 3500775380987604720000
  rows := #[⟨.path 13, 12545940579900⟩, ⟨.path 14, 69835298988000⟩, ⟨.privateRow 3 27, 20810164764759650280⟩, ⟨.privateRow 6 20, 19327952414010240⟩, ⟨.privateRow 7 18, 4502534369172840⟩, ⟨.privateRow 7 19, 208610104577578704⟩, ⟨.privateRow 8 17, 66191301149893920⟩, ⟨.privateRow 9 15, 19952180542213920⟩, ⟨.privateRow 9 16, 70488970526374400⟩, ⟨.privateRow 17 1, 37346982029280⟩, ⟨.privateRow 18 0, 190884574816320⟩, ⟨.privateRow 19 0, 323673844253760⟩, ⟨.privateRow 20 0, 838609505566560⟩, ⟨.privateRow 21 0, 2635629874637760⟩, ⟨.privateRow 22 0, 10762155321437520⟩, ⟨.privateRow 23 0, 53906867279700435⟩, ⟨.privateRow 24 0, 416758973927095800⟩, ⟨.privateRow 25 0, 4667700507983472960⟩, ⟨.hall 11 16, 1633044380767800⟩, ⟨.hall 12 16, 5832895734545880⟩, ⟨.hall 13 16, 30647177140900320⟩, ⟨.hall 11 17, 7319352464574150⟩, ⟨.hall 12 17, 25132322024409600⟩, ⟨.hall 10 18, 26279961250823280⟩, ⟨.hall 10 19, 313197283500781680⟩, ⟨.hall 9 20, 1565749102017260160⟩, ⟨.hall 8 21, 2889274570731188640⟩, ⟨.hall 7 22, 5142772792886929200⟩, ⟨.hall 6 23, 8413973830002440700⟩, ⟨.hall 5 24, 13022515429091440272⟩, ⟨.hall 4 25, 17843416992057222720⟩, ⟨.hall 3 26, 20010604955521740560⟩, ⟨.mean 12, 122438147617500⟩, ⟨.mean 15, 137700058335840⟩, ⟨.unionRow 4, 50735875086776880⟩, ⟨.tail 2 24, 44343154825842993120⟩, ⟨.tail 3 0, 637141119339744059040⟩, ⟨.tail 4 0, 8980249890359507760⟩, ⟨.tail 4 1, 76103812630165320⟩, ⟨.tail 4 6, 24277116229022737080⟩, ⟨.tail 4 14, 25114258167954555600⟩, ⟨.tail 4 20, 13064487834845046600⟩, ⟨.tail 4 22, 4287181444832646360⟩, ⟨.tail 4 26, 5682418009719010560⟩, ⟨.tail 5 0, 2808922538895192720⟩, ⟨.tail 5 8, 3302444232921113280⟩, ⟨.tail 5 15, 3242483653273104240⟩, ⟨.tail 5 18, 1406767445587904400⟩, ⟨.tail 5 20, 940919865245680320⟩, ⟨.tail 5 23, 50735875086776880⟩, ⟨.tail 5 24, 2098620287680316400⟩, ⟨.tail 5 25, 6282023806199100960⟩, ⟨.tail 6 1, 668791080689331600⟩, ⟨.tail 6 9, 786296245933598400⟩, ⟨.tail 6 15, 700638275007871200⟩, ⟨.tail 6 22, 647925677515116000⟩, ⟨.tail 6 23, 2239187214327663600⟩, ⟨.tail 6 24, 5019776732070500400⟩, ⟨.tail 7 2, 65890746865944000⟩, ⟨.tail 7 3, 134417123606525760⟩, ⟨.tail 7 13, 253679375433884400⟩, ⟨.tail 7 21, 501428583649833840⟩, ⟨.tail 7 22, 1624536363979849320⟩, ⟨.tail 7 23, 3133105013475637200⟩, ⟨.tail 8 2, 31436822123146440⟩, ⟨.tail 8 4, 13108790692277280⟩, ⟨.tail 8 8, 28766512908052920⟩, ⟨.tail 8 13, 33985753646644800⟩, ⟨.tail 8 19, 204642788029439760⟩, ⟨.tail 8 20, 521317185401212200⟩, ⟨.tail 8 21, 1173115389267221400⟩, ⟨.tail 8 22, 1873828802846080080⟩, ⟨.tail 9 1, 2481499472612160⟩, ⟨.tail 9 3, 12191714800224960⟩, ⟨.tail 9 7, 6635313807202080⟩, ⟨.tail 9 12, 6419531244366240⟩, ⟨.tail 9 18, 104708488616091360⟩, ⟨.tail 9 19, 338724678011559840⟩, ⟨.tail 9 20, 661589337654685440⟩, ⟨.tail 9 21, 902294786498064960⟩, ⟨.tail 10 1, 1085259360144960⟩, ⟨.tail 10 3, 6711472358791200⟩, ⟨.tail 10 15, 36241950737472480⟩, ⟨.tail 10 16, 85535573253530400⟩, ⟨.tail 10 17, 143682627391823520⟩, ⟨.tail 10 18, 256635279217437120⟩, ⟨.tail 10 19, 413969326981610400⟩, ⟨.tail 10 20, 430162539013247040⟩, ⟨.tail 11 0, 17849660528700⟩, ⟨.tail 11 2, 1070979631722000⟩, ⟨.tail 11 3, 124947623700900⟩, ⟨.tail 11 7, 785385063262800⟩, ⟨.tail 11 9, 356993210574000⟩, ⟨.tail 11 12, 1767116392341300⟩, ⟨.tail 11 13, 7139864211480000⟩, ⟨.tail 11 14, 19188385068352500⟩, ⟨.tail 11 15, 56851168783909500⟩, ⟨.tail 11 16, 103510181405931300⟩, ⟨.tail 11 17, 149883599459493900⟩, ⟨.tail 11 18, 196953154273675800⟩, ⟨.tail 11 19, 119610575202818700⟩, ⟨.tail 12 1, 91628257380660⟩, ⟨.tail 12 2, 706846556936520⟩, ⟨.tail 12 10, 484320789012060⟩, ⟨.tail 12 11, 2460873198223440⟩, ⟨.tail 12 12, 7382619594670320⟩, ⟨.tail 12 13, 16479996577464420⟩, ⟨.tail 12 14, 31729556555817120⟩, ⟨.tail 12 15, 61116047672900220⟩, ⟨.tail 12 16, 85724779655134620⟩, ⟨.tail 12 17, 82295264878887060⟩, ⟨.tail 13 1, 123417652798440⟩, ⟨.tail 13 2, 11219786618040⟩, ⟨.tail 13 3, 44879146472160⟩, ⟨.tail 13 5, 89758292944320⟩, ⟨.tail 13 9, 897582929443200⟩, ⟨.tail 13 10, 2535671775677040⟩, ⟨.tail 13 11, 6069904560359640⟩, ⟨.tail 13 12, 8089466151606840⟩, ⟨.tail 13 13, 24167420375258160⟩, ⟨.tail 13 14, 30540259174304880⟩, ⟨.tail 13 15, 44217179061695640⟩, ⟨.tail 13 16, 39920000786986320⟩, ⟨.tail 14 1, 112197866180400⟩, ⟨.tail 14 7, 258055092214920⟩, ⟨.tail 14 8, 796604849880840⟩, ⟨.tail 14 9, 2333715616552320⟩, ⟨.tail 14 10, 4555233366924240⟩, ⟨.tail 14 11, 7775312126301720⟩, ⟨.tail 14 12, 9301203106355160⟩, ⟨.tail 14 13, 20588308444103400⟩, ⟨.tail 14 14, 19556088075243720⟩, ⟨.tail 14 15, 10681236860374080⟩, ⟨.tail 15 0, 13089751054380⟩, ⟨.tail 15 2, 52359004217520⟩, ⟨.tail 15 5, 78538506326280⟩, ⟨.tail 15 6, 301064274250740⟩, ⟨.tail 15 7, 850833818534700⟩, ⟨.tail 15 8, 1688577886015020⟩, ⟨.tail 15 9, 3377155772030040⟩, ⟨.tail 15 10, 405782282685780⟩, ⟨.tail 15 11, 12461443003769760⟩, ⟨.tail 15 12, 7421888847833460⟩, ⟨.tail 15 15, 10288544328742680⟩, ⟨.tail 16 4, 124947623700900⟩, ⟨.tail 16 5, 339143550045300⟩, ⟨.tail 16 6, 696136760619300⟩, ⟨.tail 16 7, 1356574200181200⟩, ⟨.tail 16 8, 2266906887144900⟩, ⟨.tail 16 9, 3587781766268700⟩, ⟨.tail 16 12, 2802396703005900⟩, ⟨.tail 17 2, 28559456845920⟩, ⟨.tail 17 3, 85678370537760⟩, ⟨.tail 17 4, 285594568459200⟩, ⟨.tail 17 5, 571189136918400⟩, ⟨.tail 17 6, 1028140446453120⟩, ⟨.tail 17 11, 1056699903299040⟩, ⟨.tail 25 0, 2333850253991736480⟩, ⟨.releaseUpper 3 24, 583462563497934120⟩, ⟨.tailUpper 17 0, 85678370537760⟩, ⟨.tailUpper 18 0, 269728203544800⟩, ⟨.tailUpper 19 0, 364133074785480⟩, ⟨.tailUpper 20 0, 658907468659440⟩, ⟨.tailUpper 21 0, 2196358228864800⟩, ⟨.tailUpper 22 0, 4612352280616080⟩, ⟨.tailUpper 23 0, 25367937543388440⟩, ⟨.assumptionRow 18, 542452525546932⟩]
  caps := #[0, 11305164012483650400, 0, 335490427703520180, 136211754193540872, 6311900790235656, 0, 3134194914486636, 582022970402328, 688965359989816, 0, 323843793868140, 134772001363764, 0, 398799568942320, 24168833217144, 0, 397232275252428, 0, 1564472189621880, 0, 20426131528442640, 0, 602488516655475450, 1750387690493802360, 0, 0] }

theorem case_56_30_18_checked :
    (Witness.linear .conditional case_56_30_18).check 56 30 18 = true := by
  change case_56_30_18.check 56 30 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_30_19 : Certificate := {
  objectiveScale := 4988412000000
  eta := 16801621626037248000
  rows := #[⟨.count 2, 4557439866062603520⟩, ⟨.count 3, 1241744848299315360⟩, ⟨.count 4, 341054656376353920⟩, ⟨.count 5, 94529874637598400⟩, ⟨.count 6, 26445240136972800⟩, ⟨.count 7, 7761618685941120⟩, ⟨.count 8, 2324335007554560⟩, ⟨.count 9, 703417173338880⟩, ⟨.count 10, 214597493510400⟩, ⟨.count 11, 63608239094400⟩, ⟨.count 12, 22616262789120⟩, ⟨.count 13, 8531581275360⟩, ⟨.count 14, 4240549272960⟩, ⟨.count 15, 2650343295600⟩, ⟨.count 16, 2570029862400⟩, ⟨.count 17, 2184525383040⟩, ⟨.count 18, 4369050766080⟩, ⟨.path 13, 712345233600⟩, ⟨.path 14, 183049526400⟩, ⟨.privateRow 3 27, 71756925694534080⟩, ⟨.privateRow 6 20, 117600283120320⟩, ⟨.privateRow 7 19, 1474944727370400⟩, ⟨.privateRow 8 17, 408415224737520⟩, ⟨.privateRow 8 18, 1501424295763392⟩, ⟨.privateRow 9 15, 110925344449920⟩, ⟨.privateRow 9 16, 474446549857280⟩, ⟨.privateRow 9 17, 1165565654373120⟩, ⟨.privateRow 10 13, 28013325500160⟩, ⟨.privateRow 10 14, 148529368690560⟩, ⟨.privateRow 10 15, 400838990872320⟩, ⟨.privateRow 10 16, 799047984518784⟩, ⟨.privateRow 11 11, 5996736345600⟩, ⟨.privateRow 11 12, 45156227816700⟩, ⟨.privateRow 11 13, 138793085917200⟩, ⟨.privateRow 11 14, 299636033697000⟩, ⟨.privateRow 11 15, 505830064980240⟩, ⟨.privateRow 12 9, 677309953320⟩, ⟨.privateRow 12 10, 12891793314400⟩, ⟨.privateRow 12 11, 47735627579640⟩, ⟨.privateRow 12 12, 114503244158160⟩, ⟨.privateRow 12 13, 211556291506560⟩, ⟨.privateRow 12 14, 313282356843456⟩, ⟨.privateRow 13 8, 2806839756864⟩, ⟨.privateRow 13 9, 15974979271680⟩, ⟨.privateRow 13 10, 44071422801120⟩, ⟨.privateRow 13 11, 89404913838240⟩, ⟨.privateRow 13 12, 145280881540080⟩, ⟨.privateRow 13 13, 190612689819552⟩, ⟨.privateRow 14 6, 293717698560⟩, ⟨.privateRow 14 7, 4720135202640⟩, ⟨.privateRow 14 8, 16866840825120⟩, ⟨.privateRow 14 9, 38682391433400⟩, ⟨.privateRow 14 10, 69211822062240⟩, ⟨.privateRow 14 11, 101411389656720⟩, ⟨.privateRow 14 12, 7925788522080⟩, ⟨.privateRow 15 5, 963761198400⟩, ⟨.privateRow 15 6, 6060451669272⟩, ⟨.privateRow 15 7, 13709800504400⟩, ⟨.privateRow 15 8, 40447183516740⟩, ⟨.privateRow 15 9, 17391300292080⟩, ⟨.privateRow 16 3, 33463930500⟩, ⟨.privateRow 16 4, 1869112627200⟩, ⟨.privateRow 16 5, 7099707494880⟩, ⟨.privateRow 16 6, 14483189120400⟩, ⟨.privateRow 17 2, 299836817280⟩, ⟨.privateRow 17 3, 2803668940800⟩, ⟨.privateRow 17 4, 3186837029376⟩, ⟨.privateRow 18 1, 950673083360⟩, ⟨.privateRow 18 2, 397186433280⟩, ⟨.privateRow 19 0, 227554727400⟩, ⟨.hall 10 14, 200156436480⟩, ⟨.hall 11 14, 1065896291460⟩, ⟨.hall 10 15, 1753684012080⟩, ⟨.hall 11 15, 238355392275⟩, ⟨.hall 9 16, 1704271181184⟩, ⟨.hall 9 17, 10068070515360⟩, ⟨.hall 12 17, 727018614241920⟩, ⟨.hall 8 19, 182186579899584⟩, ⟨.hall 7 21, 3100890608786880⟩, ⟨.hall 6 22, 4887157545784800⟩, ⟨.hall 5 24, 168696914369727744⟩, ⟨.hall 4 25, 215323457753416320⟩, ⟨.hall 3 26, 225091169353450400⟩, ⟨.hall 2 27, 102009845586654720⟩, ⟨.assumptionRow 19, 2323952104320⟩]
  caps := #[0, 122285905102670400, 21877589478850560, 0, 0, 82106413435200, 0, 13341208589280, 0, 5137360271680, 283941620352, 274876709400, 566695805936, 73538201928, 250248888960, 310503481288, 0, 139426721280, 212289904480, 0, 4988412000000, 0, 0, 0, 0, 0, 0] }

theorem case_56_30_19_checked :
    (Witness.linear .conditional case_56_30_19).check 56 30 19 = true := by
  change case_56_30_19.check 56 30 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_31_1_checked :
    (Witness.rising).check 56 31 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_31_2_checked :
    (Witness.rising).check 56 31 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_31_3_checked :
    (Witness.rising).check 56 31 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_31_4_checked :
    (Witness.rising).check 56 31 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_31_5_checked :
    (Witness.rising).check 56 31 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_31_6_checked :
    (Witness.rising).check 56 31 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_31_7_checked :
    (Witness.rising).check 56 31 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_31_8_checked :
    (Witness.rising).check 56 31 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_31_9_checked :
    (Witness.rising).check 56 31 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_31_10_checked :
    (Witness.rising).check 56 31 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_31_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_31_11_checked :
    (Witness.linear .positive case_56_31_11).check 56 31 11 = true := by
  change case_56_31_11.check 56 31 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_31_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_31_12_checked :
    (Witness.linear .positive case_56_31_12).check 56 31 12 = true := by
  change case_56_31_12.check 56 31 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_31_13 : Certificate := {
  objectiveScale := 51267270600000
  eta := 307627190959225737600
  rows := #[⟨.count 2, 70199275356286876800⟩, ⟨.count 3, 10870261111111802400⟩, ⟨.count 4, 1714923422761348800⟩, ⟨.count 5, 281203029931824000⟩, ⟨.count 6, 50896710768103200⟩, ⟨.count 7, 9863132104425600⟩, ⟨.count 8, 2089862616441600⟩, ⟨.count 9, 512720957548800⟩, ⟨.count 10, 143359478262000⟩, ⟨.count 11, 61841343564000⟩, ⟨.count 12, 53006865912000⟩, ⟨.path 13, 8475936899976⟩, ⟨.path 14, 10092708741024⟩, ⟨.privateRow 4 27, 72453880313614800⟩, ⟨.privateRow 5 23, 7860195393850800⟩, ⟨.privateRow 6 19, 118588520793600⟩, ⟨.privateRow 6 20, 2814624423210600⟩, ⟨.privateRow 6 21, 4062398015435760⟩, ⟨.privateRow 6 22, 6744722120136000⟩, ⟨.privateRow 7 16, 172031373914400⟩, ⟨.privateRow 7 17, 685053506837700⟩, ⟨.privateRow 7 18, 1107086256619200⟩, ⟨.privateRow 7 19, 1766734903533600⟩, ⟨.privateRow 7 20, 2354372231571360⟩, ⟨.privateRow 7 21, 2514934847224800⟩, ⟨.privateRow 8 13, 60819172596000⟩, ⟨.privateRow 8 14, 192420277489440⟩, ⟨.privateRow 8 15, 325302124747600⟩, ⟨.privateRow 8 16, 479059589858850⟩, ⟨.privateRow 8 17, 589821853420800⟩, ⟨.privateRow 8 18, 841042272470400⟩, ⟨.privateRow 8 19, 805361691214080⟩, ⟨.privateRow 8 20, 600516925608600⟩, ⟨.privateRow 9 10, 17067634214400⟩, ⟨.privateRow 9 11, 55969539225600⟩, ⟨.privateRow 9 12, 98264702390400⟩, ⟨.privateRow 9 13, 144371427520320⟩, ⟨.privateRow 9 14, 184066490608000⟩, ⟨.privateRow 9 15, 216632100484800⟩, ⟨.privateRow 9 16, 261286369344000⟩, ⟨.privateRow 9 17, 9244968532800⟩, ⟨.privateRow 10 7, 4216455243000⟩, ⟨.privateRow 10 8, 16986291121800⟩, ⟨.privateRow 10 9, 31136900256000⟩, ⟨.privateRow 10 10, 46872927451350⟩, ⟨.privateRow 10 11, 61330258080000⟩, ⟨.privateRow 10 12, 50091488286840⟩, ⟨.privateRow 11 4, 760615455600⟩, ⟨.privateRow 11 5, 4989472037550⟩, ⟨.privateRow 11 6, 11993472691200⟩, ⟨.privateRow 11 7, 15781589623800⟩, ⟨.privateRow 11 8, 5362466155200⟩, ⟨.privateRow 12 2, 2110458550200⟩, ⟨.privateRow 12 3, 3897563670000⟩, ⟨.privateRow 13 0, 1115934019200⟩, ⟨.privateRow 14 0, 564424961100⟩, ⟨.privateRow 15 0, 628334506800⟩, ⟨.privateRow 16 0, 948702429675⟩, ⟨.privateRow 17 0, 1699075297920⟩, ⟨.privateRow 18 0, 3640875638400⟩, ⟨.privateRow 19 0, 9452273292000⟩, ⟨.privateRow 20 0, 30264778744200⟩, ⟨.privateRow 21 0, 122631311275200⟩, ⟨.privateRow 22 0, 653719220874720⟩, ⟨.privateRow 23 0, 4882717637397600⟩, ⟨.privateRow 24 0, 51684675900407550⟩, ⟨.privateRow 25 6, 8820851353669555200⟩, ⟨.hall 14 8, 28265160⟩, ⟨.hall 6 18, 87516700128⟩, ⟨.hall 6 19, 30906840276⟩, ⟨.hall 5 22, 20119643165160⟩, ⟨.hall 7 23, 769362533339400⟩, ⟨.hall 4 26, 100801889737348800⟩]
  caps := #[0, 506211440619011400, 0, 0, 1190702866593240, 154611346415760, 85092965040600, 11831691989988, 40647641248942, 0, 22065944229630, 0, 1840170744048, 0, 0, 0, 737879667525, 1699075297920, 4551094548000, 14493485714400, 56206017667800, 273562155921600, 1743251255665920, 0, 86141126500679250, 0] }

theorem case_56_31_13_checked :
    (Witness.linear .positive case_56_31_13).check 56 31 13 = true := by
  change case_56_31_13.check 56 31 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_31_14 : Certificate := {
  objectiveScale := 51806926080000
  eta := 438837354845060371200
  rows := #[⟨.count 2, 106769054926708574400⟩, ⟨.count 3, 18145066507412644800⟩, ⟨.count 4, 3207582310425292800⟩, ⟨.count 5, 593535546571968000⟩, ⟨.count 6, 115801690554950400⟩, ⟨.count 7, 23855017182796800⟩, ⟨.count 8, 5352087188448000⟩, ⟨.count 9, 1322280364204800⟩, ⟨.count 10, 371048061384000⟩, ⟨.count 11, 123682687128000⟩, ⟨.count 12, 53006865912000⟩, ⟨.count 13, 53006865912000⟩, ⟨.path 14, 1454047725312⟩, ⟨.path 15, 13666362353280⟩, ⟨.privateRow 4 27, 173235593531800800⟩, ⟨.privateRow 5 23, 5292012740414400⟩, ⟨.privateRow 6 20, 1573768494698400⟩, ⟨.privateRow 6 21, 8685126791621280⟩, ⟨.privateRow 6 22, 14202828310671000⟩, ⟨.privateRow 7 17, 309246874536600⟩, ⟨.privateRow 7 18, 2019905791675200⟩, ⟨.privateRow 7 19, 3274057417831200⟩, ⟨.privateRow 7 20, 6209513401291200⟩, ⟨.privateRow 7 21, 7397349078319200⟩, ⟨.privateRow 8 14, 32494815072720⟩, ⟨.privateRow 8 15, 473617239295200⟩, ⟨.privateRow 8 16, 852988895658900⟩, ⟨.privateRow 8 17, 1461811568817600⟩, ⟨.privateRow 8 18, 2153577940113600⟩, ⟨.privateRow 8 19, 2776713805625760⟩, ⟨.privateRow 8 20, 2695158191325600⟩, ⟨.privateRow 9 12, 100309044326400⟩, ⟨.privateRow 9 13, 222478918421760⟩, ⟨.privateRow 9 14, 401115031116800⟩, ⟨.privateRow 9 15, 547202191536000⟩, ⟨.privateRow 9 16, 844254809798400⟩, ⟨.privateRow 9 17, 932992229769600⟩, ⟨.privateRow 9 18, 948683689873920⟩, ⟨.privateRow 9 19, 281097016200000⟩, ⟨.privateRow 10 9, 16865820972000⟩, ⟨.privateRow 10 10, 59030373402000⟩, ⟨.privateRow 10 11, 111774395350800⟩, ⟨.privateRow 10 12, 167814918671400⟩, ⟨.privateRow 10 13, 231249145327200⟩, ⟨.privateRow 10 14, 310331105884800⟩, ⟨.privateRow 10 15, 163598463428400⟩, ⟨.privateRow 11 6, 1649102495040⟩, ⟨.privateRow 11 7, 15902059773600⟩, ⟨.privateRow 11 8, 31828831372800⟩, ⟨.privateRow 11 9, 53783229099600⟩, ⟨.privateRow 11 10, 76560605503200⟩, ⟨.privateRow 11 11, 55769648014080⟩, ⟨.privateRow 12 4, 3478575575475⟩, ⟨.privateRow 12 5, 9953511487920⟩, ⟨.privateRow 12 6, 18173782598400⟩, ⟨.privateRow 12 7, 13591504080000⟩, ⟨.privateRow 13 2, 4029481209600⟩, ⟨.privateRow 13 3, 3261960979200⟩, ⟨.privateRow 14 0, 1374252079200⟩, ⟨.privateRow 15 0, 793685692800⟩, ⟨.privateRow 16 0, 1159525191825⟩, ⟨.privateRow 17 0, 1998912115200⟩, ⟨.privateRow 18 0, 4095985093200⟩, ⟨.privateRow 19 0, 11342727950400⟩, ⟨.privateRow 20 0, 34588318564800⟩, ⟨.privateRow 21 0, 132064489065600⟩, ⟨.privateRow 22 0, 762672424353840⟩, ⟨.privateRow 23 0, 5326601058979200⟩, ⟨.privateRow 24 0, 68912901200543400⟩, ⟨.privateRow 25 6, 11026064192086944000⟩, ⟨.hall 7 18, 343675332000⟩, ⟨.hall 6 19, 253406794680⟩, ⟨.hall 6 20, 3740460062976⟩, ⟨.hall 8 22, 6648555513600⟩, ⟨.hall 4 25, 9597814961750400⟩, ⟨.hall 5 25, 135932091959664000⟩]
  caps := #[0, 0, 0, 2060206029423360, 738617820988320, 576471976080000, 0, 89854210130256, 9783336246684, 9908896676224, 0, 20542989458880, 254107893312, 0, 1948259275872, 7912141080480, 0, 0, 69631746584400, 0, 0, 2641289781312000, 0, 117185223297542400, 0, 0] }

theorem case_56_31_14_checked :
    (Witness.linear .positive case_56_31_14).check 56 31 14 = true := by
  change case_56_31_14.check 56 31 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_31_15 : Certificate := {
  objectiveScale := 191456720000000
  eta := 2264753585054658297600
  rows := #[⟨.count 2, 532742668214334177600⟩, ⟨.count 3, 111555005978201385600⟩, ⟨.count 4, 22747249822370673600⟩, ⟨.count 5, 5072031034342272000⟩, ⟨.count 6, 1094668400098072800⟩, ⟨.count 7, 255695965428103200⟩, ⟨.count 8, 59637542956992000⟩, ⟨.count 9, 15260194815465600⟩, ⟨.count 10, 3946602107448000⟩, ⟨.count 11, 1205906199498000⟩, ⟨.count 12, 413453554113600⟩, ⟨.count 13, 206726777056800⟩, ⟨.count 14, 160787493266400⟩, ⟨.path 16, 46286231723550⟩, ⟨.privateRow 8 16, 3411557361862650⟩, ⟨.privateRow 8 17, 9300616818292800⟩, ⟨.privateRow 8 18, 15806709880962000⟩, ⟨.privateRow 8 19, 24476241588598800⟩, ⟨.privateRow 9 13, 159813023610240⟩, ⟨.privateRow 9 14, 1968428705443200⟩, ⟨.privateRow 9 15, 4290102661244400⟩, ⟨.privateRow 9 16, 8597606566348800⟩, ⟨.privateRow 9 18, 41142108883075200⟩, ⟨.privateRow 10 12, 1346229829985040⟩, ⟨.privateRow 10 13, 1598130236102400⟩, ⟨.privateRow 10 14, 3557423288519100⟩, ⟨.privateRow 10 15, 5603548547797200⟩, ⟨.privateRow 10 16, 2793682695503700⟩, ⟨.privateRow 10 17, 7459077983076720⟩, ⟨.privateRow 10 18, 19949525513968050⟩, ⟨.privateRow 11 9, 152869927310100⟩, ⟨.privateRow 11 10, 307622352819600⟩, ⟨.privateRow 11 11, 1027578252420720⟩, ⟨.privateRow 11 12, 1344768125500800⟩, ⟨.privateRow 11 13, 2335072913573400⟩, ⟨.privateRow 11 15, 8861583435705000⟩, ⟨.privateRow 12 6, 18867920128200⟩, ⟨.privateRow 12 7, 78626851102800⟩, ⟨.privateRow 12 8, 185192737780050⟩, ⟨.privateRow 12 9, 286076449058400⟩, ⟨.privateRow 12 10, 825184385085060⟩, ⟨.privateRow 12 11, 946221636960600⟩, ⟨.privateRow 12 12, 1486566511404975⟩, ⟨.privateRow 12 13, 344544628428000⟩, ⟨.privateRow 12 15, 5347332633202560⟩, ⟨.privateRow 13 4, 19435850834400⟩, ⟨.privateRow 13 5, 46570317908400⟩, ⟨.privateRow 13 6, 92150397662400⟩, ⟨.privateRow 13 7, 162554388796800⟩, ⟨.privateRow 13 8, 255396717576000⟩, ⟨.privateRow 13 9, 637142528262240⟩, ⟨.privateRow 13 10, 704991316629600⟩, ⟨.privateRow 13 11, 1025020269573300⟩, ⟨.privateRow 13 12, 463431456259200⟩, ⟨.privateRow 13 14, 1894465387694880⟩, ⟨.privateRow 13 15, 746071637711400⟩, ⟨.privateRow 14 3, 64697824671480⟩, ⟨.privateRow 14 4, 33634118489400⟩, ⟨.privateRow 14 5, 84810985459200⟩, ⟨.privateRow 14 6, 159351890647950⟩, ⟨.privateRow 14 7, 226042157741400⟩, ⟨.privateRow 14 8, 538063861395060⟩, ⟨.privateRow 14 9, 612523783872000⟩, ⟨.privateRow 14 11, 1535684629564800⟩, ⟨.privateRow 14 12, 626879810056500⟩, ⟨.privateRow 14 14, 350287038901800⟩, ⟨.privateRow 15 0, 17196523344000⟩, ⟨.privateRow 15 1, 7765305072525⟩, ⟨.privateRow 15 2, 63340527650400⟩, ⟨.privateRow 15 3, 32888350895400⟩, ⟨.privateRow 15 4, 96135179540400⟩, ⟨.privateRow 15 5, 169314102757800⟩, ⟨.privateRow 15 6, 236530361995200⟩, ⟨.privateRow 15 7, 527675318810640⟩, ⟨.privateRow 15 8, 648022321346400⟩, ⟨.privateRow 15 9, 231132021570450⟩, ⟨.privateRow 15 10, 1002311646336000⟩, ⟨.privateRow 15 11, 1233922202112600⟩, ⟨.privateRow 15 14, 214383324355200⟩, ⟨.privateRow 16 0, 82220877238500⟩, ⟨.privateRow 16 3, 80112649617000⟩, ⟨.privateRow 16 4, 160787493266400⟩, ⟨.privateRow 16 5, 232211689655400⟩, ⟨.privateRow 16 6, 521828500873680⟩, ⟨.privateRow 16 8, 1795155819707250⟩, ⟨.privateRow 17 0, 244267060477440⟩, ⟨.privateRow 17 2, 155915144985600⟩, ⟨.privateRow 17 4, 1054198991664000⟩, ⟨.privateRow 17 5, 481388010143040⟩, ⟨.privateRow 17 6, 426601160585600⟩, ⟨.privateRow 17 7, 1763790077649600⟩, ⟨.privateRow 17 10, 3063732598967040⟩, ⟨.privateRow 18 0, 831257419192200⟩, ⟨.privateRow 18 3, 1419403642347600⟩, ⟨.privateRow 18 4, 1259014795758720⟩, ⟨.privateRow 18 6, 3815353225633950⟩, ⟨.privateRow 18 7, 922961974334400⟩, ⟨.privateRow 18 10, 2691972425142000⟩, ⟨.privateRow 19 0, 2842613654680800⟩, ⟨.privateRow 19 2, 1403805800124000⟩, ⟨.privateRow 19 5, 6895590904402200⟩, ⟨.privateRow 19 6, 1643075163100800⟩, ⟨.privateRow 20 0, 2613579821552700⟩, ⟨.privateRow 20 5, 4046833272081600⟩, ⟨.privateRow 20 8, 3709597166074800⟩, ⟨.privateRow 21 0, 16309964399601600⟩, ⟨.privateRow 21 1, 17940960839561760⟩, ⟨.privateRow 21 3, 36084263342727600⟩, ⟨.privateRow 21 5, 127250423999899200⟩, ⟨.privateRow 21 8, 41817277144843200⟩, ⟨.privateRow 21 9, 74866415533509600⟩, ⟨.privateRow 22 2, 72590071817963700⟩, ⟨.privateRow 22 3, 108252790028182800⟩, ⟨.privateRow 22 5, 264865237657740720⟩, ⟨.privateRow 22 6, 97376925609463500⟩, ⟨.privateRow 22 7, 313966814692330800⟩, ⟨.privateRow 23 0, 1125244473709356000⟩, ⟨.privateRow 23 3, 60590087045888400⟩, ⟨.privateRow 23 5, 1012720026338420400⟩, ⟨.privateRow 24 0, 17469420454337751900⟩, ⟨.privateRow 24 4, 32699171619657843300⟩, ⟨.privateRow 25 6, 5633216195737219689600⟩, ⟨.hall 21 1, 170675193250041480⟩, ⟨.hall 15 2, 41293151679780⟩, ⟨.hall 19 2, 6039592080303600⟩, ⟨.hall 22 2, 441442062762901200⟩, ⟨.hall 15 4, 3511704866670⟩, ⟨.hall 18 5, 95407491160800⟩, ⟨.hall 22 6, 84084202431028800⟩, ⟨.hall 23 6, 1706414696394408000⟩, ⟨.hall 13 7, 180902071350⟩, ⟨.hall 12 8, 42270228000⟩, ⟨.hall 22 8, 536655056692154400⟩, ⟨.hall 19 9, 1578878132668200⟩, ⟨.hall 21 9, 631710673771937760⟩, ⟨.hall 17 11, 417487073203200⟩, ⟨.hall 18 12, 21847984487128800⟩, ⟨.hall 14 13, 20165994428580⟩, ⟨.hall 8 14, 215737936960⟩, ⟨.hall 16 14, 19458210094202880⟩, ⟨.hall 15 15, 16519544585168625⟩, ⟨.hall 13 17, 32666659048623600⟩, ⟨.hall 12 18, 42360855368832000⟩, ⟨.hall 11 19, 63595473274192860⟩, ⟨.hall 7 20, 35761619520900⟩, ⟨.hall 9 20, 8002547303587200⟩, ⟨.hall 10 20, 111627239237514000⟩, ⟨.hall 8 22, 328352211150163200⟩, ⟨.hall 7 23, 872882412592390200⟩, ⟨.hall 6 24, 1965627856915474752⟩, ⟨.hall 5 25, 2546392012740576000⟩]
  caps := #[0, 1731589613743298400, 0, 43262736952744400, 10050553303363300, 0, 0, 140025906438600, 243312892272450, 39828168700320, 29806460811400, 30255548491350, 15746117609950, 108878218521840, 35829189693375, 1554187603150, 222706552231800, 45998342557440, 144535522466790, 0, 11624426381295000, 0, 0, 258435269236544400, 7166941724856513600, 0] }

theorem case_56_31_15_checked :
    (Witness.linear .positive case_56_31_15).check 56 31 15 = true := by
  change case_56_31_15.check 56 31 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_31_16 : Certificate := {
  objectiveScale := 130319280000000
  eta := 1447722228421015747200
  rows := #[⟨.count 2, 348791163943016995200⟩, ⟨.count 3, 83043042159750472800⟩, ⟨.count 4, 21302530344237542400⟩, ⟨.count 5, 5469969639430296000⟩, ⟨.count 6, 1406274562048356000⟩, ⟨.count 7, 362298073463726400⟩, ⟨.count 8, 93100830949526400⟩, ⟨.count 9, 26486085254428800⟩, ⟨.count 10, 7673948542260000⟩, ⟨.count 11, 2331418652362800⟩, ⟨.count 12, 757998182541600⟩, ⟨.count 13, 275635702742400⟩, ⟨.count 14, 160787493266400⟩, ⟨.count 15, 109627836318000⟩, ⟨.path 17, 18617195142000⟩, ⟨.privateRow 3 28, 7322744805831655200⟩, ⟨.privateRow 8 17, 10057918951080000⟩, ⟨.privateRow 8 18, 26056912576695000⟩, ⟨.privateRow 8 19, 50741609465907360⟩, ⟨.privateRow 9 15, 3914931843622800⟩, ⟨.privateRow 9 16, 12428664414566400⟩, ⟨.privateRow 9 17, 24472181298364800⟩, ⟨.privateRow 9 18, 42030825209493120⟩, ⟨.privateRow 9 19, 45205647349262400⟩, ⟨.privateRow 9 20, 54018101273136000⟩, ⟨.privateRow 10 12, 153478970845200⟩, ⟨.privateRow 10 14, 7306695290594700⟩, ⟨.privateRow 10 15, 8752999674018600⟩, ⟨.privateRow 10 16, 17489294153931600⟩, ⟨.privateRow 10 17, 27766538382623040⟩, ⟨.privateRow 11 10, 114278714222400⟩, ⟨.privateRow 11 11, 551062590558480⟩, ⟨.privateRow 11 12, 859969471561200⟩, ⟨.privateRow 11 13, 5303246581883250⟩, ⟨.privateRow 11 14, 6701915060240400⟩, ⟨.privateRow 11 16, 11515307926842720⟩, ⟨.privateRow 12 8, 64123583624100⟩, ⟨.privateRow 12 9, 241181239899600⟩, ⟨.privateRow 12 10, 673010507529360⟩, ⟨.privateRow 12 11, 971743461288600⟩, ⟨.privateRow 12 12, 1255434489834525⟩, ⟨.privateRow 12 13, 9726822998263800⟩, ⟨.privateRow 12 15, 5322066027117840⟩, ⟨.privateRow 13 6, 33435100036800⟩, ⟨.privateRow 13 7, 110872694532600⟩, ⟨.privateRow 13 8, 294429046111200⟩, ⟨.privateRow 13 9, 637672596921360⟩, ⟨.privateRow 13 10, 874613287548000⟩, ⟨.privateRow 13 11, 1098567296026200⟩, ⟨.privateRow 13 12, 5717926350021600⟩, ⟨.privateRow 13 13, 3162742999416000⟩, ⟨.privateRow 13 14, 2105432714024640⟩, ⟨.privateRow 14 4, 18457747951500⟩, ⟨.privateRow 14 5, 53890313677200⟩, ⟨.privateRow 14 7, 578417345906400⟩, ⟨.privateRow 14 8, 450204981145920⟩, ⟨.privateRow 14 10, 2572599892262400⟩, ⟨.privateRow 14 11, 2939293818232200⟩, ⟨.privateRow 14 12, 4012030784361600⟩, ⟨.privateRow 14 14, 5762508910458300⟩, ⟨.privateRow 15 3, 46983358422000⟩, ⟨.privateRow 15 4, 69149865985200⟩, ⟨.privateRow 15 6, 581359738050000⟩, ⟨.privateRow 15 7, 515981682936720⟩, ⟨.privateRow 15 8, 122620765066800⟩, ⟨.privateRow 15 9, 1869154609221900⟩, ⟨.privateRow 15 10, 3036169028692800⟩, ⟨.privateRow 15 11, 3787032701251800⟩, ⟨.privateRow 15 13, 425721431034900⟩, ⟨.privateRow 15 15, 25722344661413400⟩, ⟨.privateRow 16 0, 12333131585775⟩, ⟨.privateRow 16 2, 57946142053800⟩, ⟨.privateRow 16 3, 97821761637600⟩, ⟨.privateRow 16 5, 637834684032000⟩, ⟨.privateRow 16 6, 688462812077040⟩, ⟨.privateRow 16 7, 315484551181800⟩, ⟨.privateRow 16 8, 1555344927761625⟩, ⟨.privateRow 16 9, 217689560688600⟩, ⟨.privateRow 16 10, 10449359931710700⟩, ⟨.privateRow 17 0, 54570300744960⟩, ⟨.privateRow 17 1, 32018288702400⟩, ⟨.privateRow 17 2, 191895563059200⟩, ⟨.privateRow 17 4, 779575724928000⟩, ⟨.privateRow 17 6, 2793479680992000⟩, ⟨.privateRow 17 9, 11547465425496000⟩, ⟨.privateRow 18 0, 263280819601800⟩, ⟨.privateRow 18 1, 219817866668400⟩, ⟨.privateRow 18 3, 1216093836812400⟩, ⟨.privateRow 18 4, 414149603868000⟩, ⟨.privateRow 18 5, 3142935327131600⟩, ⟨.privateRow 18 8, 15993077202702600⟩, ⟨.privateRow 19 0, 1376250991315200⟩, ⟨.privateRow 19 2, 1713611218082400⟩, ⟨.privateRow 19 3, 1640032431317280⟩, ⟨.privateRow 19 5, 10276826598838800⟩, ⟨.privateRow 19 8, 9669801608026560⟩, ⟨.privateRow 19 11, 119275085913984000⟩, ⟨.privateRow 20 1, 12968261167352400⟩, ⟨.privateRow 20 4, 12519890435502450⟩, ⟨.privateRow 20 6, 23325497332137000⟩, ⟨.privateRow 20 11, 257311148883188400⟩, ⟨.privateRow 21 0, 28573095527121600⟩, ⟨.privateRow 21 2, 41967159858624000⟩, ⟨.privateRow 21 4, 28713245597150400⟩, ⟨.privateRow 21 5, 29451953257927200⟩, ⟨.privateRow 21 6, 63400387929278400⟩, ⟨.privateRow 21 9, 123428414798488800⟩, ⟨.privateRow 22 0, 99855610988613480⟩, ⟨.privateRow 22 1, 258884917377886800⟩, ⟨.privateRow 22 3, 62725915717264800⟩, ⟨.privateRow 22 4, 155803080975141600⟩, ⟨.privateRow 22 6, 139868674966320300⟩, ⟨.privateRow 22 8, 1391604791437060200⟩, ⟨.privateRow 23 1, 2239669289017660500⟩, ⟨.privateRow 23 2, 1758349056719455200⟩, ⟨.privateRow 23 6, 328917615391965600⟩, ⟨.privateRow 23 8, 7634350967781938400⟩, ⟨.privateRow 24 0, 8958677156070642000⟩, ⟨.privateRow 24 1, 21842108113848422400⟩, ⟨.privateRow 25 2, 937435977611231978880⟩, ⟨.hall 19 3, 393953087471580⟩, ⟨.hall 20 3, 1209962271248640⟩, ⟨.hall 22 5, 46576053307383600⟩, ⟨.hall 19 7, 269788884805440⟩, ⟨.hall 21 9, 56655665809142400⟩, ⟨.hall 20 10, 82162978554384000⟩, ⟨.hall 12 11, 417221654850⟩, ⟨.hall 15 13, 181016439253650⟩, ⟨.hall 16 13, 507837900810240⟩, ⟨.hall 17 13, 35900854232443200⟩, ⟨.hall 13 15, 56861123319000⟩, ⟨.hall 15 15, 7927462913745375⟩, ⟨.hall 8 16, 2016377126400⟩, ⟨.hall 12 17, 655037770186800⟩, ⟨.hall 13 17, 6408530088760800⟩, ⟨.hall 9 19, 3757453750552320⟩, ⟨.hall 11 19, 306822734025607800⟩, ⟨.hall 10 20, 515668460547240000⟩, ⟨.hall 8 22, 1040444641341705600⟩, ⟨.hall 7 23, 2654429763551365800⟩, ⟨.hall 5 24, 287428927273488000⟩, ⟨.hall 6 24, 4851262789905980448⟩, ⟨.hall 4 26, 9302020982664009600⟩, ⟨.hall 3 27, 9225768152028027600⟩]
  caps := #[0, 0, 133316371054994400, 0, 15219191157206400, 2182528657764000, 1823085728755200, 0, 579612231318120, 0, 33524634780000, 58354349098500, 5301388310400, 194529251570400, 0, 63566441691480, 4795719221475, 0, 1283859174925600, 0, 5005863655794300, 0, 191330904742957980, 20402784413411400, 6057772172200148400, 0] }

theorem case_56_31_16_checked :
    (Witness.linear .positive case_56_31_16).check 56 31 16 = true := by
  change case_56_31_16.check 56 31 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_31_17 : Certificate := {
  objectiveScale := 73419091200000
  eta := 532926435950868960000
  rows := #[⟨.count 2, 138560873347225929600⟩, ⟨.count 3, 36030461213200053600⟩, ⟨.count 4, 9457864416677476800⟩, ⟨.count 5, 2512668402139896000⟩, ⟨.count 6, 680075519621097600⟩, ⟨.count 7, 187915604105829600⟩, ⟨.count 8, 55925063431036800⟩, ⟨.count 9, 17216630048217600⟩, ⟨.count 10, 5543233159464000⟩, ⟨.count 11, 1912958894246400⟩, ⟨.count 12, 666119614960800⟩, ⟨.count 13, 256199851908000⟩, ⟨.count 14, 119559930890400⟩, ⟨.count 15, 163036269396000⟩, ⟨.path 15, 10241365837248⟩, ⟨.privateRow 2 29, 888210726584781600⟩, ⟨.privateRow 5 23, 169266583976490000⟩, ⟨.privateRow 6 21, 65299286618485920⟩, ⟨.privateRow 6 22, 206755997760912600⟩, ⟨.privateRow 7 19, 24165856940425200⟩, ⟨.privateRow 7 20, 73360731413249280⟩, ⟨.privateRow 7 21, 145173316994105400⟩, ⟨.privateRow 8 17, 8763587661628800⟩, ⟨.privateRow 8 18, 26474070959736400⟩, ⟨.privateRow 8 19, 52488258872169120⟩, ⟨.privateRow 8 20, 84187853609359500⟩, ⟨.privateRow 9 14, 135259719795200⟩, ⟨.privateRow 9 15, 3025228554348000⟩, ⟨.privateRow 9 16, 9730418617920000⟩, ⟨.privateRow 9 17, 19561936975380800⟩, ⟨.privateRow 9 18, 31358033752805760⟩, ⟨.privateRow 9 19, 41490919047177600⟩, ⟨.privateRow 10 12, 86409222779880⟩, ⟨.privateRow 10 13, 1125856015884600⟩, ⟨.privateRow 10 14, 3582722019977100⟩, ⟨.privateRow 10 15, 7545085638690600⟩, ⟨.privateRow 10 16, 12301086525928200⟩, ⟨.privateRow 10 17, 16742194504275240⟩, ⟨.privateRow 10 18, 18549451550529900⟩, ⟨.privateRow 11 10, 39029894794800⟩, ⟨.privateRow 11 11, 433676476593360⟩, ⟨.privateRow 11 12, 1392450508248800⟩, ⟨.privateRow 11 13, 2980846458790200⟩, ⟨.privateRow 11 14, 5060335256776800⟩, ⟨.privateRow 11 15, 7069433792421000⟩, ⟨.privateRow 11 16, 8232244696035360⟩, ⟨.privateRow 11 17, 4749789981736800⟩, ⟨.privateRow 12 8, 14233325106000⟩, ⟨.privateRow 12 9, 172352627647200⟩, ⟨.privateRow 12 10, 566201672716680⟩, ⟨.privateRow 12 11, 1247788167626000⟩, ⟨.privateRow 12 12, 2181434989058325⟩, ⟨.privateRow 12 13, 3201888149202600⟩, ⟨.privateRow 12 14, 1742870659229700⟩, ⟨.privateRow 13 6, 3941536183200⟩, ⟨.privateRow 13 7, 70947651297600⟩, ⟨.privateRow 13 8, 241866993060000⟩, ⟨.privateRow 13 9, 553391680121280⟩, ⟨.privateRow 13 10, 1011223005223200⟩, ⟨.privateRow 13 11, 747413798739300⟩, ⟨.privateRow 14 5, 30218444071200⟩, ⟨.privateRow 14 6, 109240770188550⟩, ⟨.privateRow 14 7, 260858031033600⟩, ⟨.privateRow 14 8, 280965837592440⟩, ⟨.privateRow 15 3, 12421811001600⟩, ⟨.privateRow 15 4, 52673256266400⟩, ⟨.privateRow 15 5, 86952677011200⟩, ⟨.privateRow 16 0, 6113860102350⟩, ⟨.privateRow 16 1, 1630362693960⟩, ⟨.privateRow 16 2, 20961806065200⟩, ⟨.privateRow 17 0, 5796845134080⟩, ⟨.privateRow 18 0, 4399391396400⟩, ⟨.privateRow 19 0, 12182930020800⟩, ⟨.privateRow 20 0, 41794218265800⟩, ⟨.privateRow 21 0, 182374770614400⟩, ⟨.privateRow 22 0, 1053214300298160⟩, ⟨.privateRow 23 0, 4290873075288800⟩, ⟨.privateRow 24 0, 55513170411548850⟩, ⟨.privateRow 25 0, 1522646959859625600⟩, ⟨.hall 9 17, 8676446775360⟩, ⟨.hall 8 18, 21424587649920⟩, ⟨.hall 9 18, 16889799719520⟩, ⟨.hall 8 19, 84753492751200⟩, ⟨.hall 7 21, 900866680131600⟩, ⟨.hall 7 22, 22510346830171200⟩, ⟨.hall 6 23, 68090304514276044⟩, ⟨.hall 5 25, 3130129752919092000⟩, ⟨.hall 4 26, 5216141342069257600⟩, ⟨.hall 3 27, 6752608256768774400⟩, ⟨.hall 2 28, 5390520271686950400⟩, ⟨.assumptionRow 17, 94272595872000⟩]
  caps := #[0, 7534352795424436800, 108475243148956320, 0, 153379252388544, 3315989899593280, 0, 188831284256160, 123129155082752, 55102879383552, 78428720649552, 0, 78115022114467, 19958884841280, 26333371620192, 102001398960048, 0, 0, 148208744938800, 219292740374400, 794090147050200, 3647495412288000, 0, 94399207656353600, 1276802919465623550, 0] }

theorem case_56_31_17_checked :
    (Witness.linear .conditional case_56_31_17).check 56 31 17 = true := by
  change case_56_31_17.check 56 31 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_31_18 : Certificate := {
  objectiveScale := 677378520000000
  eta := 7186512988797467925600
  rows := #[⟨.path 13, 97830553260258⟩, ⟨.privateRow 2 29, 79161781006868660100⟩, ⟨.privateRow 5 23, 2345721397277157900⟩, ⟨.privateRow 6 21, 731507484618991080⟩, ⟨.privateRow 6 22, 2195105483201781150⟩, ⟨.privateRow 7 19, 228608874674680500⟩, ⟨.privateRow 7 20, 731425655939018040⟩, ⟨.privateRow 7 21, 1508818572852891300⟩, ⟨.privateRow 8 17, 71259142143189000⟩, ⟨.privateRow 8 18, 246224771057765500⟩, ⟨.privateRow 8 19, 530747637361801860⟩, ⟨.privateRow 8 20, 911946543016208700⟩, ⟨.privateRow 9 15, 21704656241868600⟩, ⟨.privateRow 9 16, 83705926160656800⟩, ⟨.privateRow 9 17, 190877429666523600⟩, ⟨.privateRow 9 18, 337413341691185760⟩, ⟨.privateRow 18 0, 51142924983150⟩, ⟨.hall 12 18, 13982444022947400⟩, ⟨.hall 11 19, 247723693307500410⟩, ⟨.hall 10 20, 749394271370745000⟩, ⟨.hall 9 21, 1775284151678200800⟩, ⟨.hall 8 22, 3519321074121652800⟩, ⟨.hall 7 23, 6997298281807108275⟩, ⟨.hall 6 24, 13768821006983602560⟩, ⟨.hall 5 25, 24678585702792252000⟩, ⟨.hall 4 26, 40491603933703722800⟩, ⟨.hall 3 27, 59323235834204842500⟩, ⟨.hall 2 28, 69785797949083616400⟩, ⟨.mean 5, 141708521307478125⟩, ⟨.mean 6, 41398168292709800⟩, ⟨.unionRow 5, 21816581934747600⟩, ⟨.tail 2 26, 158323562013737320200⟩, ⟨.tail 3 0, 644966495538003639000⟩, ⟨.tail 3 28, 19753034202091990800⟩, ⟨.tail 4 0, 22079321287875551700⟩, ⟨.tail 4 8, 23181246749562501600⟩, ⟨.tail 4 13, 17916491765947074300⟩, ⟨.tail 4 19, 15712640842573174500⟩, ⟨.tail 4 26, 7346169744579666000⟩, ⟨.tail 4 27, 23630179345064592300⟩, ⟨.tail 5 0, 4205585007214390800⟩, ⟨.tail 5 2, 38868622987194000⟩, ⟨.tail 5 3, 202116839533408800⟩, ⟨.tail 5 12, 5029599814542903600⟩, ⟨.tail 5 18, 2992883970013938000⟩, ⟨.tail 5 25, 5915804418650926800⟩, ⟨.tail 5 26, 16822340028857563200⟩, ⟨.tail 6 1, 1088321443641432000⟩, ⟨.tail 6 15, 1148567809271582700⟩, ⟨.tail 6 24, 3676971734588552400⟩, ⟨.tail 6 25, 9888177687942153600⟩, ⟨.tail 7 1, 137472182354707200⟩, ⟨.tail 7 9, 180432239340553200⟩, ⟨.tail 7 15, 125197880358751200⟩, ⟨.tail 7 23, 2051649578624045400⟩, ⟨.tail 7 24, 5078492450826795000⟩, ⟨.tail 8 0, 7637343464150400⟩, ⟨.tail 8 1, 45824060784902400⟩, ⟨.tail 8 11, 50120066483487000⟩, ⟨.tail 8 22, 1016005347715257900⟩, ⟨.tail 8 23, 2233922963263992000⟩, ⟨.tail 9 1, 12916095564372000⟩, ⟨.tail 9 2, 224627748945600⟩, ⟨.tail 9 9, 13253037187790400⟩, ⟨.tail 9 20, 497662777788976800⟩, ⟨.tail 9 21, 928274172517692000⟩, ⟨.tail 9 22, 1233094027836871200⟩, ⟨.tail 10 1, 7265303754959250⟩, ⟨.tail 10 14, 6444008547876900⟩, ⟨.tail 10 15, 34999811132586300⟩, ⟨.tail 10 16, 105252139615322700⟩, ⟨.tail 10 17, 234764076116770200⟩, ⟨.tail 10 18, 430864100946279000⟩, ⟨.tail 10 19, 582424654930168050⟩, ⟨.tail 10 20, 846755358501902850⟩, ⟨.tail 10 21, 770248551134462400⟩, ⟨.tail 11 1, 926589464400600⟩, ⟨.tail 11 4, 379059326345700⟩, ⟨.tail 11 8, 884471761473300⟩, ⟨.tail 11 12, 1853178928801200⟩, ⟨.tail 11 13, 8170834367896200⟩, ⟨.tail 11 14, 25060033241743500⟩, ⟨.tail 11 15, 63850437637786800⟩, ⟨.tail 11 16, 135029355584923800⟩, ⟨.tail 11 17, 240829025338301400⟩, ⟨.tail 11 18, 358337416505468400⟩, ⟨.tail 11 19, 393758404667327700⟩, ⟨.tail 11 20, 296213804687700900⟩, ⟨.tail 12 1, 728034579171900⟩, ⟨.tail 12 10, 463294732200300⟩, ⟨.tail 12 11, 2614305988844550⟩, ⟨.tail 12 12, 8206935256119600⟩, ⟨.tail 12 13, 19557656195026950⟩, ⟨.tail 12 14, 40670658991012050⟩, ⟨.tail 12 15, 77105480430478500⟩, ⟨.tail 12 16, 129722525016084000⟩, ⟨.tail 12 17, 186674684595849450⟩, ⟨.tail 12 18, 205669768616061750⟩, ⟨.tail 12 19, 69262562463944850⟩, ⟨.tail 13 1, 274922148778200⟩, ⟨.tail 13 9, 916407162594000⟩, ⟨.tail 13 10, 2779768393201800⟩, ⟨.tail 13 11, 6964694435714400⟩, ⟨.tail 13 12, 14509780074405000⟩, ⟨.tail 13 13, 26423073188127000⟩, ⟨.tail 13 14, 44262465953290200⟩, ⟨.tail 13 15, 69005459343328200⟩, ⟨.tail 13 16, 95031422760997800⟩, ⟨.tail 13 17, 101110256939538000⟩, ⟨.tail 13 18, 30730186852318800⟩, ⟨.tail 14 1, 132369923485800⟩, ⟨.tail 14 7, 264739846971600⟩, ⟨.tail 14 8, 860404502657700⟩, ⟨.tail 14 9, 2647398469716000⟩, ⟨.tail 14 10, 5460259343789250⟩, ⟨.tail 14 11, 10291761551020950⟩, ⟨.tail 14 12, 17472829900125600⟩, ⟨.tail 14 13, 27036556871974650⟩, ⟨.tail 14 14, 39049127428311000⟩, ⟨.tail 14 15, 959681945272050⟩, ⟨.tail 14 17, 45435976236500850⟩, ⟨.tail 15 1, 84235405854600⟩, ⟨.tail 15 5, 84235405854600⟩, ⟨.tail 15 6, 336941623418400⟩, ⟨.tail 15 7, 968707167327900⟩, ⟨.tail 15 8, 2021649740510400⟩, ⟨.tail 15 9, 4296005698584600⟩, ⟨.tail 15 10, 7412715715204800⟩, ⟨.tail 15 11, 12256251551844300⟩, ⟨.tail 15 12, 18910848614357700⟩, ⟨.tail 15 15, 1853178928801200⟩, ⟨.tail 16 1, 63176554390950⟩, ⟨.tail 16 4, 126353108781900⟩, ⟨.tail 16 5, 379059326345700⟩, ⟨.tail 16 6, 884471761473300⟩, ⟨.tail 16 7, 1768943522946600⟩, ⟨.tail 16 8, 3158827719547500⟩, ⟨.tail 16 9, 6001772667140250⟩, ⟨.tail 16 11, 758118652691400⟩, ⟨.tail 17 2, 112313874472800⟩, ⟨.tail 17 3, 224627748945600⟩, ⟨.tail 17 4, 449255497891200⟩, ⟨.tail 17 5, 786197121309600⟩, ⟨.tail 17 7, 112313874472800⟩, ⟨.tail 17 12, 1347766493673600⟩, ⟨.tail 18 1, 238666983254700⟩, ⟨.assumptionRow 18, 597009726213264⟩]
  caps := #[0, 0, 11859072523333995960, 0, 62334775853810460, 88171492716234200, 7201609042557436, 5360071055312610, 231636480430992, 87906059188584, 751158974209644, 0, 66615176621448, 644640966216450, 564250041408690, 0, 1184603958736380, 1528786871430000, 0, 677378520000000, 0, 0, 0, 0, 0, 0] }

theorem case_56_31_18_checked :
    (Witness.linear .conditional case_56_31_18).check 56 31 18 = true := by
  change case_56_31_18.check 56 31 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_31_19 : Certificate := {
  objectiveScale := 15460378926300000000
  eta := 62981491346834231092521600
  rows := #[⟨.count 2, 15943427840943885543861600⟩, ⟨.count 3, 4081655304675885362025600⟩, ⟨.count 4, 1070906109857424467827200⟩, ⟨.count 5, 283494881838823206552000⟩, ⟨.count 6, 78003029618374432572000⟩, ⟨.count 7, 22001533651272109334400⟩, ⟨.count 8, 6372479159919012940800⟩, ⟨.count 9, 1890415977967861344000⟩, ⟨.count 10, 563489378048112516000⟩, ⟨.count 11, 213277700078425382400⟩, ⟨.count 12, 85691933067224484000⟩, ⟨.count 13, 39989568764704759200⟩, ⟨.count 14, 19994784382352379600⟩, ⟨.count 15, 9088538355614718000⟩, ⟨.count 16, 14541661368983548800⟩, ⟨.path 10, 341426613832920000⟩, ⟨.path 12, 3432493383495064560⟩, ⟨.privateRow 2 29, 1832008789176781879263600⟩, ⟨.privateRow 5 22, 380229821795660316480⟩, ⟨.privateRow 5 23, 50296577162528890393200⟩, ⟨.privateRow 6 21, 14683581059344176339360⟩, ⟨.privateRow 6 22, 48248648159107411115100⟩, ⟨.privateRow 7 19, 4080407491638413535600⟩, ⟨.privateRow 7 20, 15178586136945028237440⟩, ⟨.privateRow 7 21, 34962308691427589472000⟩, ⟨.privateRow 8 17, 1088402959964615895600⟩, ⟨.privateRow 8 18, 4712407137386231283000⟩, ⟨.privateRow 8 19, 11718357420691590068400⟩, ⟨.privateRow 8 20, 22853887073389509637500⟩, ⟨.privateRow 9 15, 267404995174086369600⟩, ⟨.privateRow 9 16, 1440316935594561024000⟩, ⟨.privateRow 9 17, 3952908282135361348800⟩, ⟨.privateRow 9 18, 8118124820257882510080⟩, ⟨.privateRow 9 19, 13891325957759562312000⟩, ⟨.privateRow 10 13, 54733197652701968400⟩, ⟨.privateRow 10 14, 426366055607775458175⟩, ⟨.privateRow 10 15, 1337183664635371152600⟩, ⟨.privateRow 10 16, 2950896928428838689300⟩, ⟨.privateRow 10 17, 5257174126421777479920⟩, ⟨.privateRow 10 18, 7732755646415892442350⟩, ⟨.privateRow 11 11, 5331942501960634560⟩, ⟨.privateRow 11 12, 118218321129329220800⟩, ⟨.privateRow 11 13, 448822319128106823900⟩, ⟨.privateRow 11 14, 1094346575524160758800⟩, ⟨.privateRow 11 15, 2074105436510785477800⟩, ⟨.privateRow 11 16, 3241942221703474008720⟩, ⟨.privateRow 11 17, 4076966830689502249500⟩, ⟨.privateRow 12 10, 24660234071567934840⟩, ⟨.privateRow 12 11, 146575522548937682200⟩, ⟨.privateRow 12 12, 410666687567302891725⟩, ⟨.privateRow 12 13, 847534023717263110800⟩, ⟨.privateRow 12 14, 1417487392820338339500⟩, ⟨.privateRow 12 15, 1964916025231457418120⟩, ⟨.privateRow 12 16, 2152652768592901725150⟩, ⟨.privateRow 13 8, 3116070293353617600⟩, ⟨.privateRow 13 9, 41967074912409939600⟩, ⟨.privateRow 13 10, 153317760587512752000⟩, ⟨.privateRow 13 11, 356225760218558191500⟩, ⟨.privateRow 13 12, 648559238474356149600⟩, ⟨.privateRow 13 13, 977254241808526743600⟩, ⟨.privateRow 13 14, 475831923718926519360⟩, ⟨.privateRow 14 7, 9694440912655699200⟩, ⟨.privateRow 14 8, 53271818390124554220⟩, ⟨.privateRow 14 9, 151230392987157283800⟩, ⟨.privateRow 14 10, 309383583344791730775⟩, ⟨.privateRow 14 11, 386157774568016365200⟩, ⟨.privateRow 15 5, 1262296993835377500⟩, ⟨.privateRow 15 6, 16744943394587116800⟩, ⟨.privateRow 15 7, 61559699795363689920⟩, ⟨.privateRow 15 8, 150465801665176998000⟩, ⟨.privateRow 15 9, 64907311423015111050⟩, ⟨.privateRow 16 4, 4241317899286868400⟩, ⟨.privateRow 16 5, 23630199724598266800⟩, ⟨.privateRow 16 6, 57984874708821900840⟩, ⟨.privateRow 17 2, 621438520042032000⟩, ⟨.privateRow 17 3, 8482635798573736800⟩, ⟨.privateRow 17 4, 12925921216874265600⟩, ⟨.privateRow 18 1, 2905225081196499600⟩, ⟨.privateRow 18 2, 1430603259680094500⟩, ⟨.privateRow 19 0, 679143525474506400⟩, ⟨.hall 10 16, 2722229164945290000⟩, ⟨.hall 10 17, 6049914253762579200⟩, ⟨.hall 9 18, 39476684467616891040⟩, ⟨.hall 9 19, 36121235036895066240⟩, ⟨.hall 11 19, 1436625257872018474260⟩, ⟨.hall 8 21, 6291542073682819262400⟩, ⟨.hall 7 23, 281570189087628455414400⟩, ⟨.hall 5 24, 36010000770059594678400⟩, ⟨.hall 6 24, 522885340995360379100064⟩, ⟨.hall 4 26, 1437094765031218896803200⟩, ⟨.hall 3 27, 2046824659453763941151400⟩, ⟨.hall 2 28, 2127383924803606916647200⟩, ⟨.assumptionRow 19, 9596019203418211200⟩]
  caps := #[0, 0, 0, 0, 3360859387310471482800, 300176113741843933440, 0, 6198021562379828832, 0, 8497272627238127040, 1680694637969131260, 0, 4560974405722975925, 1699410848331934080, 5617885249851367935, 4315657023120492000, 1313357315803860600, 9596019203418211200, 36450569290682329300, 4944281652219823200, 15460378926300000000, 0, 0, 0, 0, 0] }

theorem case_56_31_19_checked :
    (Witness.linear .conditional case_56_31_19).check 56 31 19 = true := by
  change case_56_31_19.check 56 31 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_31_20 : Certificate := {
  objectiveScale := 51816765000000
  eta := 266463217975434480000
  rows := #[⟨.count 2, 69724542036905355600⟩, ⟨.count 3, 18420718112214818400⟩, ⟨.count 4, 4950107211401352000⟩, ⟨.count 5, 1331563793948388000⟩, ⟨.count 6, 364111229531649600⟩, ⟨.count 7, 100055358528325200⟩, ⟨.count 8, 27469799879121600⟩, ⟨.count 9, 7499668392216000⟩, ⟨.count 10, 1956435232752000⟩, ⟨.count 11, 478239723561600⟩, ⟨.count 12, 102479940763200⟩, ⟨.count 13, 25619985190800⟩, ⟨.path 13, 14615543330388⟩, ⟨.privateRow 2 29, 9104159947494011400⟩, ⟨.privateRow 5 22, 802448990703360⟩, ⟨.privateRow 5 23, 233587885887556200⟩, ⟨.privateRow 6 21, 67656480528677040⟩, ⟨.privateRow 6 22, 224528989078444050⟩, ⟨.privateRow 7 19, 19110956225961600⟩, ⟨.privateRow 7 20, 69797224382165280⟩, ⟨.privateRow 7 21, 163317506960708100⟩, ⟨.privateRow 8 17, 5292467849869200⟩, ⟨.privateRow 8 18, 21513390544345700⟩, ⟨.privateRow 8 19, 53827873552372920⟩, ⟨.privateRow 8 20, 107796637614215550⟩, ⟨.privateRow 9 15, 1419321300797400⟩, ⟨.privateRow 9 16, 6558716208844800⟩, ⟨.privateRow 9 17, 17826506463365600⟩, ⟨.privateRow 9 18, 37531673820600960⟩, ⟨.privateRow 9 19, 66834001367733600⟩, ⟨.privateRow 10 13, 361849942353900⟩, ⟨.privateRow 10 14, 1960511139486900⟩, ⟨.privateRow 10 15, 5910647037995700⟩, ⟨.privateRow 10 16, 13314628667340000⟩, ⟨.privateRow 10 17, 24793740668396700⟩, ⟨.privateRow 10 18, 39311101481426775⟩, ⟨.privateRow 11 11, 84507132970260⟩, ⟨.privateRow 11 12, 565796238607600⟩, ⟨.privateRow 11 13, 1946585124809325⟩, ⟨.privateRow 11 14, 4798700862555600⟩, ⟨.privateRow 11 15, 9504561627260700⟩, ⟨.privateRow 11 16, 15853103381835720⟩, ⟨.privateRow 11 17, 22073072922850950⟩, ⟨.privateRow 12 9, 16497717736500⟩, ⟨.privateRow 12 10, 152865911638440⟩, ⟨.privateRow 12 11, 628164081344800⟩, ⟨.privateRow 12 12, 1744827741431775⟩, ⟨.privateRow 12 13, 3757902827807700⟩, ⟨.privateRow 12 14, 6688595300437050⟩, ⟨.privateRow 12 15, 10021684207134600⟩, ⟨.privateRow 12 16, 12159351721491975⟩, ⟨.privateRow 13 7, 1970768091600⟩, ⟨.privateRow 13 8, 36011307855600⟩, ⟨.privateRow 13 9, 193332349785960⟩, ⟨.privateRow 13 10, 631959634706400⟩, ⟨.privateRow 13 11, 1522911042783900⟩, ⟨.privateRow 13 12, 2952210601216800⟩, ⟨.privateRow 13 13, 4788309539890800⟩, ⟨.privateRow 13 14, 6488951018402160⟩, ⟨.privateRow 13 15, 546888145419000⟩, ⟨.privateRow 14 6, 5515413478575⟩, ⟨.privateRow 14 7, 53180878350600⟩, ⟨.privateRow 14 8, 222253371530190⟩, ⟨.privateRow 14 9, 624842972153400⟩, ⟨.privateRow 14 10, 1354656716963550⟩, ⟨.privateRow 14 11, 2417733602469900⟩, ⟨.privateRow 14 12, 1677041530614450⟩, ⟨.privateRow 15 5, 9963327574200⟩, ⟨.privateRow 15 6, 71637148674000⟩, ⟨.privateRow 15 7, 253249671795120⟩, ⟨.privateRow 15 8, 637954883766200⟩, ⟨.privateRow 15 9, 1250624049825150⟩, ⟨.privateRow 16 4, 16643285834175⟩, ⟨.privateRow 16 5, 95969076758100⟩, ⟨.privateRow 16 6, 300801917035620⟩, ⟨.privateRow 16 7, 335582987840100⟩, ⟨.privateRow 17 3, 27776549600800⟩, ⟨.privateRow 17 4, 134381409926400⟩, ⟨.privateRow 17 5, 65214507758400⟩, ⟨.privateRow 18 2, 47476765486150⟩, ⟨.privateRow 18 3, 12598257180600⟩, ⟨.privateRow 19 1, 13198174189200⟩, ⟨.hall 10 18, 624778275221100⟩, ⟨.hall 9 19, 298603397645280⟩, ⟨.hall 10 19, 527635831372650⟩, ⟨.hall 11 19, 27270125736964110⟩, ⟨.hall 9 20, 13078190787480000⟩, ⟨.hall 8 22, 730630265102337600⟩, ⟨.hall 7 23, 1425557890980323100⟩, ⟨.hall 6 24, 2578057964269836048⟩, ⟨.hall 5 25, 4363605731537514000⟩, ⟨.hall 4 26, 6889971920802370400⟩, ⟨.hall 3 27, 9754457086600726500⟩, ⟨.hall 2 28, 10183795399635858000⟩, ⟨.assumptionRow 20, 1878969015000⟩]
  caps := #[0, 2282699238209289900, 57491371875597660, 40861443984641280, 0, 1144130742694940, 0, 0, 0, 0, 36461695087545, 37798104414070, 12255962838119, 0, 1878969015000, 5611598984250, 35565551965125, 1878969015000, 36239884485350, 5820071103000, 516288680985000, 51816765000000, 0, 0, 0, 0] }

theorem case_56_31_20_checked :
    (Witness.linear .conditional case_56_31_20).check 56 31 20 = true := by
  change case_56_31_20.check 56 31 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_32_1_checked :
    (Witness.rising).check 56 32 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_32_2_checked :
    (Witness.rising).check 56 32 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_32_3_checked :
    (Witness.rising).check 56 32 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_32_4_checked :
    (Witness.rising).check 56 32 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_32_5_checked :
    (Witness.rising).check 56 32 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_32_6_checked :
    (Witness.rising).check 56 32 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_32_7_checked :
    (Witness.rising).check 56 32 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_32_8_checked :
    (Witness.rising).check 56 32 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_32_9_checked :
    (Witness.rising).check 56 32 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_32_10_checked :
    (Witness.rising).check 56 32 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_32_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_32_11_checked :
    (Witness.linear .positive case_56_32_11).check 56 32 11 = true := by
  change case_56_32_11.check 56 32 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_32_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_32_12_checked :
    (Witness.linear .positive case_56_32_12).check 56 32 12 = true := by
  change case_56_32_12.check 56 32 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_32_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_32_13_checked :
    (Witness.linear .positive case_56_32_13).check 56 32 13 = true := by
  change case_56_32_13.check 56 32 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_32_14 : Certificate := {
  objectiveScale := 7512004281600000
  eta := 89926006802349628310400
  rows := #[⟨.count 2, 17991828184847401684800⟩, ⟨.count 3, 3104064782267746096800⟩, ⟨.count 4, 558546626101550486400⟩, ⟨.count 5, 103920655010419447200⟩, ⟨.count 6, 20451204418526481600⟩, ⟨.count 7, 4254061901011322400⟩, ⟨.count 8, 932567460945120000⟩, ⟨.count 9, 223816190626828800⟩, ⟨.count 10, 55954047656707200⟩, ⟨.count 11, 18318289411422000⟩, ⟨.count 12, 6763676090371200⟩, ⟨.count 13, 7327315764568800⟩, ⟨.path 14, 645834683894400⟩, ⟨.path 15, 1682562441111552⟩, ⟨.privateRow 5 23, 137700246804696576⟩, ⟨.privateRow 5 24, 7498208751786993240⟩, ⟨.privateRow 6 21, 1540068549789369600⟩, ⟨.privateRow 6 22, 2554701947297660160⟩, ⟨.privateRow 6 23, 5243027489356456800⟩, ⟨.privateRow 7 18, 301502390721632100⟩, ⟨.privateRow 7 19, 616350963728728800⟩, ⟨.privateRow 7 20, 1127370441675878400⟩, ⟨.privateRow 7 21, 1762019605494308160⟩, ⟨.privateRow 7 22, 2401638761773251000⟩, ⟨.privateRow 7 23, 1358884014520032000⟩, ⟨.privateRow 8 15, 57663754668439920⟩, ⟨.privateRow 8 16, 149901584463030400⟩, ⟨.privateRow 8 17, 274718831203416600⟩, ⟨.privateRow 8 18, 403890526537898400⟩, ⟨.privateRow 8 19, 669117153228123600⟩, ⟨.privateRow 8 20, 818794230709815360⟩, ⟨.privateRow 8 21, 974532996687650400⟩, ⟨.privateRow 9 12, 10297099047935700⟩, ⟨.privateRow 9 13, 36666856987160400⟩, ⟨.privateRow 9 15, 252829400522899200⟩, ⟨.privateRow 9 16, 88982478565180200⟩, ⟨.privateRow 9 17, 235473283888642800⟩, ⟨.privateRow 9 18, 302307285256376400⟩, ⟨.privateRow 9 20, 740419707012885900⟩, ⟨.privateRow 10 10, 11979905075218080⟩, ⟨.privateRow 10 11, 17446782915181620⟩, ⟨.privateRow 10 12, 23187018233499120⟩, ⟨.privateRow 10 13, 29002848035393232⟩, ⟨.privateRow 10 14, 129626877071371680⟩, ⟨.privateRow 10 16, 34171936247489040⟩, ⟨.privateRow 10 17, 366887581926825960⟩, ⟨.privateRow 10 19, 63997442007358860⟩, ⟨.privateRow 10 20, 82221364473328080⟩, ⟨.privateRow 10 22, 634612157173154160⟩, ⟨.privateRow 11 7, 1687503024567360⟩, ⟨.privateRow 11 8, 5757176672161200⟩, ⟨.privateRow 11 10, 34971279785442000⟩, ⟨.privateRow 11 11, 5207844262420800⟩, ⟨.privateRow 11 13, 107985390914200800⟩, ⟨.privateRow 11 16, 85651880490376200⟩, ⟨.privateRow 12 5, 2096035038422325⟩, ⟨.privateRow 12 6, 2855774349267840⟩, ⟨.privateRow 12 7, 3301318091728800⟩, ⟨.privateRow 12 8, 5788145885029200⟩, ⟨.privateRow 12 9, 5119727040628200⟩, ⟨.privateRow 12 10, 27823303917208800⟩, ⟨.privateRow 12 12, 63910476390961200⟩, ⟨.privateRow 12 15, 43541164831764600⟩, ⟨.privateRow 13 4, 5601169262338650⟩, ⟨.privateRow 13 6, 4066257649568400⟩, ⟨.privateRow 13 8, 11108398578977700⟩, ⟨.privateRow 13 10, 40018416868029600⟩, ⟨.privateRow 13 12, 44879809057983900⟩, ⟨.privateRow 13 14, 3945477719383200⟩, ⟨.privateRow 14 1, 1091696035630200⟩, ⟨.privateRow 14 3, 6099157724484825⟩, ⟨.privateRow 14 7, 18651349218902400⟩, ⟨.privateRow 14 10, 75308523135846000⟩, ⟨.privateRow 14 12, 17794909713952800⟩, ⟨.privateRow 14 15, 21232562726875500⟩, ⟨.privateRow 15 1, 5567976310937040⟩, ⟨.privateRow 15 2, 3613698911162340⟩, ⟨.privateRow 15 6, 22381619062682880⟩, ⟨.privateRow 15 7, 1865134921890240⟩, ⟨.privateRow 15 10, 129510306138753540⟩, ⟨.privateRow 16 1, 5197120745892075⟩, ⟨.privateRow 16 2, 362665123700880⟩, ⟨.privateRow 16 3, 19595018673430200⟩, ⟨.privateRow 16 5, 26293221468313800⟩, ⟨.privateRow 16 8, 1208883745669600⟩, ⟨.privateRow 16 10, 219153353322103200⟩, ⟨.privateRow 17 2, 34305160170481200⟩, ⟨.privateRow 17 3, 2391198617808000⟩, ⟨.privateRow 17 4, 39375070573238400⟩, ⟨.privateRow 17 8, 43131245068711800⟩, ⟨.privateRow 17 9, 160756867077206400⟩, ⟨.privateRow 17 10, 219153353322103200⟩, ⟨.privateRow 18 2, 151567832388772800⟩, ⟨.privateRow 18 4, 22648066908667200⟩, ⟨.privateRow 18 7, 49070811635445600⟩, ⟨.privateRow 18 8, 210303478437624000⟩, ⟨.privateRow 19 1, 247386577002364800⟩, ⟨.privateRow 19 2, 243466719268172400⟩, ⟨.privateRow 19 5, 5032903757481600⟩, ⟨.privateRow 19 6, 63697688180626500⟩, ⟨.privateRow 19 7, 318690655786245600⟩, ⟨.privateRow 19 9, 437107691337276960⟩, ⟨.privateRow 20 0, 695121438196785600⟩, ⟨.privateRow 20 1, 831938991111708480⟩, ⟨.privateRow 20 2, 293395412225916000⟩, ⟨.privateRow 20 5, 69925906580509980⟩, ⟨.privateRow 20 7, 487688374099967040⟩, ⟨.privateRow 21 0, 9233805612554523000⟩, ⟨.privateRow 21 2, 580922916207313680⟩, ⟨.privateRow 21 4, 188262056178296100⟩, ⟨.privateRow 21 5, 399576609031485600⟩, ⟨.privateRow 21 8, 8552476266385451400⟩, ⟨.privateRow 22 0, 70786533123039333600⟩, ⟨.privateRow 23 0, 803502455768967754800⟩, ⟨.privateRow 24 0, 18798091817440317782400⟩, ⟨.hall 16 1, 10394241491784150⟩, ⟨.hall 17 1, 25416163975282080⟩, ⟨.hall 18 1, 76032796050525600⟩, ⟨.hall 19 1, 238327350238897920⟩, ⟨.hall 21 4, 18255714538501440⟩, ⟨.hall 12 5, 8379704908575⟩, ⟨.hall 19 5, 9495646389989760⟩, ⟨.hall 21 6, 449872965413071200⟩, ⟨.hall 22 7, 7179059742265691280⟩, ⟨.hall 20 8, 29122211287609440⟩, ⟨.hall 23 8, 423380446338745896000⟩, ⟨.hall 19 12, 82752552166284000⟩, ⟨.hall 15 14, 212570524186020⟩, ⟨.hall 16 14, 1709707011732720⟩, ⟨.hall 17 14, 29945777357015520⟩, ⟨.hall 14 16, 2179038348286800⟩, ⟨.hall 13 17, 374935748187000⟩, ⟨.hall 12 18, 133493607046800⟩, ⟨.hall 6 20, 266586723374400⟩, ⟨.hall 10 20, 908344929492000⟩, ⟨.hall 10 21, 14412406214606400⟩, ⟨.hall 5 22, 2443399028214144⟩, ⟨.hall 8 22, 66743898231410400⟩, ⟨.hall 7 23, 230054030754483936⟩, ⟨.hall 4 26, 3213688795714768800⟩, ⟨.hall 5 26, 6159854790511021600⟩, ⟨.hall 3 28, 98934956419214916000⟩]
  caps := #[0, 189544825122432998400, 0, 0, 0, 0, 0, 54582180631509960, 5188675162454784, 4527173350996296, 1983977542939392, 9635058861327120, 1394162875123200, 184688517031200, 166178580167418, 7283763100490877, 0, 23475948263457690, 0, 163333627587753480, 0, 0, 0, 35711220256398566880, 0] }

theorem case_56_32_14_checked :
    (Witness.linear .positive case_56_32_14).check 56 32 14 = true := by
  change case_56_32_14.check 56 32 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_32_15 : Certificate := {
  objectiveScale := 395368646400000
  eta := 5784916462246682560800
  rows := #[⟨.count 2, 1174755230552567664000⟩, ⟨.count 3, 258364000006141629600⟩, ⟨.count 4, 53828278296381388800⟩, ⟨.count 5, 12244368536894894400⟩, ⟨.count 6, 2656000573834608000⟩, ⟨.count 7, 631743805740247200⟩, ⟨.count 8, 146950024148928000⟩, ⟨.count 9, 37514645588019600⟩, ⟨.count 10, 9749568909880800⟩, ⟨.count 11, 2997538267323600⟩, ⟨.count 12, 922319466868800⟩, ⟨.count 13, 333059807480400⟩, ⟨.count 14, 423894300429600⟩, ⟨.path 15, 32750361824544⟩, ⟨.path 16, 67872005248320⟩, ⟨.privateRow 3 29, 24234461049860661600⟩, ⟨.privateRow 7 19, 67552026407236800⟩, ⟨.privateRow 7 20, 134115446719254000⟩, ⟨.privateRow 7 21, 235334004332787360⟩, ⟨.privateRow 7 22, 383301374802746400⟩, ⟨.privateRow 8 16, 6389814084253600⟩, ⟨.privateRow 8 17, 27535467265406100⟩, ⟨.privateRow 8 18, 62292276720273600⟩, ⟨.privateRow 8 19, 116994826918569600⟩, ⟨.privateRow 8 20, 176340028978713600⟩, ⟨.privateRow 8 21, 260730319289239800⟩, ⟨.privateRow 9 14, 4832395024897440⟩, ⟨.privateRow 9 15, 11617843789552000⟩, ⟨.privateRow 9 16, 23420160098735400⟩, ⟨.privateRow 9 17, 47304585383655600⟩, ⟨.privateRow 9 19, 247737958981072560⟩, ⟨.privateRow 9 20, 66675041005072500⟩, ⟨.privateRow 9 21, 114427911432634800⟩, ⟨.privateRow 10 11, 381504870386640⟩, ⟨.privateRow 10 12, 2181128854937760⟩, ⟨.privateRow 10 13, 5290200869361408⟩, ⟨.privateRow 10 14, 9344514356136960⟩, ⟨.privateRow 10 15, 18036702483279480⟩, ⟨.privateRow 10 16, 29490932044173600⟩, ⟨.privateRow 10 17, 12632050152802080⟩, ⟨.privateRow 10 18, 30528867516939792⟩, ⟨.privateRow 11 9, 361008882234000⟩, ⟨.privateRow 11 10, 1021888045678500⟩, ⟨.privateRow 11 11, 2287377686084400⟩, ⟨.privateRow 11 12, 4145080694915160⟩, ⟨.privateRow 11 13, 7441699940875200⟩, ⟨.privateRow 11 14, 12046924627387650⟩, ⟨.privateRow 11 15, 18041460480529200⟩, ⟨.privateRow 11 16, 11828669526273600⟩, ⟨.privateRow 11 17, 15902091898973280⟩, ⟨.privateRow 12 6, 23911986178080⟩, ⟨.privateRow 12 7, 215939875179600⟩, ⟨.privateRow 12 8, 541961225190000⟩, ⟨.privateRow 12 9, 1050419392822800⟩, ⟨.privateRow 12 10, 1874917098054000⟩, ⟨.privateRow 12 11, 3512499969658680⟩, ⟨.privateRow 12 13, 19291848848672400⟩, ⟨.privateRow 12 14, 6364736320971600⟩, ⟨.privateRow 12 16, 20700948034166400⟩, ⟨.privateRow 13 4, 35227479637350⟩, ⟨.privateRow 13 5, 121267929903120⟩, ⟨.privateRow 13 6, 294629829694200⟩, ⟨.privateRow 13 7, 553785833739600⟩, ⟨.privateRow 13 8, 924454465634700⟩, ⟨.privateRow 13 9, 1565148186201600⟩, ⟨.privateRow 13 10, 3246052123674360⟩, ⟨.privateRow 13 12, 12608235212022450⟩, ⟨.privateRow 13 14, 12190842953289000⟩, ⟨.privateRow 13 15, 10022538206640960⟩, ⟨.privateRow 14 3, 151390821582000⟩, ⟨.privateRow 14 4, 131205378704400⟩, ⟨.privateRow 14 5, 326571629412600⟩, ⟨.privateRow 14 6, 556652405509200⟩, ⟨.privateRow 14 7, 1009272143880000⟩, ⟨.privateRow 14 8, 1568959423668000⟩, ⟨.privateRow 14 9, 3112595291725920⟩, ⟨.privateRow 14 10, 645934172083200⟩, ⟨.privateRow 14 11, 9295396445134800⟩, ⟨.privateRow 14 12, 4835855386533600⟩, ⟨.privateRow 14 13, 7100229532195800⟩, ⟨.privateRow 15 0, 35324525035800⟩, ⟨.privateRow 15 1, 39895934158080⟩, ⟨.privateRow 15 2, 172207059549525⟩, ⟨.privateRow 15 3, 144124062146064⟩, ⟨.privateRow 15 4, 436005566156160⟩, ⟨.privateRow 15 5, 694534507626960⟩, ⟨.privateRow 15 6, 1204566303720780⟩, ⟨.privateRow 15 8, 6523733283611544⟩, ⟨.privateRow 15 9, 758299804101840⟩, ⟨.privateRow 15 11, 22339229632639920⟩, ⟨.privateRow 15 14, 4800602952365220⟩, ⟨.privateRow 16 0, 274284547336800⟩, ⟨.privateRow 16 1, 119220271995825⟩, ⟨.privateRow 16 2, 207237213543360⟩, ⟨.privateRow 16 3, 676212336399600⟩, ⟨.privateRow 16 5, 3314617932525900⟩, ⟨.privateRow 16 7, 6874152571966680⟩, ⟨.privateRow 16 9, 7400487995000100⟩, ⟨.privateRow 16 10, 13100352427562400⟩, ⟨.privateRow 17 0, 1227527244994050⟩, ⟨.privateRow 17 2, 1090013915390400⟩, ⟨.privateRow 17 4, 5145605813548200⟩, ⟨.privateRow 17 6, 3405284213451120⟩, ⟨.privateRow 17 7, 18180355551758400⟩, ⟨.privateRow 17 9, 18388938461493600⟩, ⟨.privateRow 17 11, 9240895749365280⟩, ⟨.privateRow 17 14, 133738651785538800⟩, ⟨.privateRow 18 0, 5284548945355680⟩, ⟨.privateRow 18 3, 8807581575592800⟩, ⟨.privateRow 18 4, 2932394338036800⟩, ⟨.privateRow 18 5, 4838450657760720⟩, ⟨.privateRow 18 6, 26232104432934400⟩, ⟨.privateRow 18 7, 17972613702143100⟩, ⟨.privateRow 18 8, 17598822554570400⟩, ⟨.privateRow 18 9, 21618609321909600⟩, ⟨.privateRow 18 14, 220647076095045600⟩, ⟨.privateRow 19 0, 21545076637141200⟩, ⟨.privateRow 19 3, 34814383843075200⟩, ⟨.privateRow 19 5, 45067365464721600⟩, ⟨.privateRow 19 6, 59065129040217300⟩, ⟨.privateRow 20 0, 107728777001926080⟩, ⟨.privateRow 20 5, 496816231369217760⟩, ⟨.privateRow 21 0, 374894137844226000⟩, ⟨.privateRow 21 2, 449872965413071200⟩, ⟨.privateRow 21 4, 679699371656705400⟩, ⟨.privateRow 21 6, 1639754359440397200⟩, ⟨.privateRow 22 0, 3995512068312928800⟩, ⟨.privateRow 22 2, 1506096449426368800⟩, ⟨.privateRow 22 3, 1814161632263580600⟩, ⟨.privateRow 22 4, 2718797486626821600⟩, ⟨.privateRow 22 8, 19305418124465272800⟩, ⟨.privateRow 23 0, 1204877159541095040⟩, ⟨.privateRow 23 6, 11672247483054358200⟩, ⟨.privateRow 23 9, 1271145403315855267200⟩, ⟨.privateRow 24 3, 75053806396414045200⟩, ⟨.hall 12 7, 524826322020⟩, ⟨.hall 17 7, 36368302210240⟩, ⟨.hall 23 7, 52922555792343237000⟩, ⟨.hall 15 8, 7948381404600⟩, ⟨.hall 19 12, 54165306872476800⟩, ⟨.hall 15 13, 30990591712080⟩, ⟨.hall 18 13, 41472434209377600⟩, ⟨.hall 8 17, 250550882400⟩, ⟨.hall 14 17, 54117172354845600⟩, ⟨.hall 12 18, 392390299501200⟩, ⟨.hall 13 18, 65612782073638800⟩, ⟨.hall 11 20, 297152788235846400⟩, ⟨.hall 10 21, 536303361734431200⟩, ⟨.hall 9 22, 1105120086500430000⟩, ⟨.hall 8 23, 1234427302217709600⟩, ⟨.hall 7 24, 3232990962060507648⟩, ⟨.hall 4 25, 71233269531881600⟩, ⟨.hall 6 25, 7215151469403477600⟩, ⟨.hall 5 26, 16980712253272768000⟩, ⟨.hall 3 28, 28157865907143772800⟩]
  caps := #[0, 0, 0, 308435571598321440, 0, 4609040307004224, 1143841763064000, 831926630414880, 1088842469602888, 37475889285744, 78413183157036, 0, 71625988554120, 370319943559104, 953437440704112, 22090900460265, 2016187772996670, 0, 1730973873636280, 33938162200800, 9428775640764480, 39119388296788800, 0, 16717670588632693680, 0] }

theorem case_56_32_15_checked :
    (Witness.linear .positive case_56_32_15).check 56 32 15 = true := by
  change case_56_32_15.check 56 32 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_32_16 : Certificate := {
  objectiveScale := 124925509800000
  eta := 1766651135177130602400
  rows := #[⟨.count 2, 436767970333646952000⟩, ⟨.count 3, 107001306838791565200⟩, ⟨.count 4, 25975273829067763200⟩, ⟨.count 5, 6777434022418659600⟩, ⟨.count 6, 1775814337156860000⟩, ⟨.count 7, 467202168123490800⟩, ⟨.count 8, 123777135725443200⟩, ⟨.count 9, 33063755433508800⟩, ⟨.count 10, 9325674609451200⟩, ⟨.count 11, 2831008363583400⟩, ⟨.count 12, 922319466868800⟩, ⟨.count 13, 333059807480400⟩, ⟨.count 14, 211947150214800⟩, ⟨.path 16, 19219567610880⟩, ⟨.privateRow 2 30, 18073157393116425600⟩, ⟨.privateRow 8 18, 46476982225674000⟩, ⟨.privateRow 8 19, 53222284387272000⟩, ⟨.privateRow 9 15, 3434328822925000⟩, ⟨.privateRow 9 16, 9617101940996550⟩, ⟨.privateRow 9 17, 39119388296788800⟩, ⟨.privateRow 9 18, 53192847283075500⟩, ⟨.privateRow 10 13, 1602320455623888⟩, ⟨.privateRow 10 14, 4717001576447160⟩, ⟨.privateRow 10 15, 10902031539173775⟩, ⟨.privateRow 10 16, 28049691422712960⟩, ⟨.privateRow 10 17, 39461026917492180⟩, ⟨.privateRow 10 18, 30079539558484416⟩, ⟨.privateRow 10 19, 28358528698740240⟩, ⟨.privateRow 11 10, 29016574136550⟩, ⟨.privateRow 11 11, 628960049663400⟩, ⟨.privateRow 11 12, 1934774699817960⟩, ⟨.privateRow 11 13, 4807499645348400⟩, ⟨.privateRow 11 14, 9068310212761800⟩, ⟨.privateRow 11 15, 19060104437173800⟩, ⟨.privateRow 11 17, 80830587459061440⟩, ⟨.privateRow 11 20, 91992632734302300⟩, ⟨.privateRow 12 8, 35473825648800⟩, ⟨.privateRow 12 9, 251929854376200⟩, ⟨.privateRow 12 10, 773257734849600⟩, ⟨.privateRow 12 11, 2031664825630440⟩, ⟨.privateRow 12 12, 4140474273335400⟩, ⟨.privateRow 12 13, 7106343392298150⟩, ⟨.privateRow 12 14, 13245532343643600⟩, ⟨.privateRow 12 15, 6562986206376600⟩, ⟨.privateRow 12 16, 34171936247489040⟩, ⟨.privateRow 13 6, 25619985190800⟩, ⟨.privateRow 13 7, 117260701450200⟩, ⟨.privateRow 13 8, 322384813650900⟩, ⟨.privateRow 13 9, 872244041268600⟩, ⟨.privateRow 13 10, 1916374892271840⟩, ⟨.privateRow 13 12, 12931687525056300⟩, ⟨.privateRow 13 13, 6392186305104600⟩, ⟨.privateRow 13 14, 8247500232671700⟩, ⟨.privateRow 13 15, 17629111809789480⟩, ⟨.privateRow 13 17, 28181983709880000⟩, ⟨.privateRow 14 4, 17157626445960⟩, ⟨.privateRow 14 5, 61637691644100⟩, ⟨.privateRow 14 6, 153719911144800⟩, ⟨.privateRow 14 7, 398662496832600⟩, ⟨.privateRow 14 8, 927612852238800⟩, ⟨.privateRow 14 9, 1887843545127540⟩, ⟨.privateRow 14 10, 423894300429600⟩, ⟨.privateRow 14 11, 9490312127921625⟩, ⟨.privateRow 14 13, 5202797901701400⟩, ⟨.privateRow 15 3, 59345202060144⟩, ⟨.privateRow 15 4, 19680806805660⟩, ⟨.privateRow 15 6, 1068566882332950⟩, ⟨.privateRow 15 7, 755302571674560⟩, ⟨.privateRow 15 8, 1063974694078296⟩, ⟨.privateRow 15 9, 2997874691371560⟩, ⟨.privateRow 15 10, 6753166073719065⟩, ⟨.privateRow 15 11, 4756699614106440⟩, ⟨.privateRow 15 12, 3115623108157560⟩, ⟨.privateRow 16 2, 134233195136040⟩, ⟨.privateRow 16 5, 8831131258950⟩, ⟨.privateRow 16 6, 3988460008587600⟩, ⟨.privateRow 16 8, 3410779139567800⟩, ⟨.privateRow 16 9, 7506461570107500⟩, ⟨.privateRow 16 10, 7842044557947600⟩, ⟨.privateRow 16 11, 5057294500958700⟩, ⟨.privateRow 17 0, 13246696888425⟩, ⟨.privateRow 17 1, 240206770243440⟩, ⟨.privateRow 17 4, 11774841678600⟩, ⟨.privateRow 17 5, 5491357982838000⟩, ⟨.privateRow 17 6, 1985238307011960⟩, ⟨.privateRow 17 7, 3767949337152000⟩, ⟨.privateRow 17 8, 9829049091211350⟩, ⟨.privateRow 17 9, 12797570784398400⟩, ⟨.privateRow 17 11, 3758529463809120⟩, ⟨.privateRow 18 0, 571920881532000⟩, ⟨.privateRow 18 4, 8610008907427200⟩, ⟨.privateRow 18 6, 19998166824235600⟩, ⟨.privateRow 18 8, 41545966894146000⟩, ⟨.privateRow 18 10, 24329514300371280⟩, ⟨.privateRow 19 2, 6305427718890300⟩, ⟨.privateRow 19 3, 11183652874321200⟩, ⟨.privateRow 19 4, 8698916608101720⟩, ⟨.privateRow 19 5, 30083038368583200⟩, ⟨.privateRow 19 8, 69402598973908200⟩, ⟨.privateRow 19 11, 427053322239944400⟩, ⟨.privateRow 20 1, 15158762965005660⟩, ⟨.privateRow 20 2, 32184587644176240⟩, ⟨.privateRow 20 3, 33055883110786536⟩, ⟨.privateRow 20 4, 68024269649416080⟩, ⟨.privateRow 20 7, 245800156464822960⟩, ⟨.privateRow 20 9, 116380180182946680⟩, ⟨.privateRow 20 10, 198204900703729920⟩, ⟨.privateRow 20 12, 2562319933439666400⟩, ⟨.privateRow 21 0, 45639286346253600⟩, ⟨.privateRow 21 2, 376524112356592200⟩, ⟨.privateRow 21 4, 42786830949612750⟩, ⟨.privateRow 21 5, 588187945462431600⟩, ⟨.privateRow 21 7, 749136285883505520⟩, ⟨.privateRow 21 9, 352074494671099200⟩, ⟨.privateRow 22 0, 485436045682879200⟩, ⟨.privateRow 22 2, 593310722501296800⟩, ⟨.privateRow 22 6, 15074656280167564080⟩, ⟨.privateRow 23 0, 7756396714545799320⟩, ⟨.privateRow 23 2, 3576979067387625900⟩, ⟨.privateRow 23 6, 171318471122249451000⟩, ⟨.privateRow 24 3, 484963056715290753600⟩, ⟨.privateRow 24 7, 2823177794449728315600⟩, ⟨.hall 17 3, 7918904513520⟩, ⟨.hall 23 4, 44949807127522697400⟩, ⟨.hall 20 6, 3323454525214200⟩, ⟨.hall 15 7, 2838967124175⟩, ⟨.hall 16 7, 17050876507665⟩, ⟨.hall 17 8, 28022790046160⟩, ⟨.hall 21 9, 188573233130656920⟩, ⟨.hall 22 9, 1204877159541095040⟩, ⟨.hall 17 11, 160137846828960⟩, ⟨.hall 20 11, 228196431731268000⟩, ⟨.hall 14 13, 34973258750430⟩, ⟨.hall 16 13, 328013446761000⟩, ⟨.hall 10 14, 1017083847780⟩, ⟨.hall 13 14, 27394083236520⟩, ⟨.hall 15 14, 468465539371830⟩, ⟨.hall 13 17, 555099679134000⟩, ⟨.hall 8 18, 33483535940400⟩, ⟨.hall 9 18, 201453407391600⟩, ⟨.hall 10 19, 2550430707584760⟩, ⟨.hall 8 20, 1103670338206800⟩, ⟨.hall 11 20, 497004532714918800⟩, ⟨.hall 7 24, 5759485771481009568⟩, ⟨.hall 6 25, 10519829106463076400⟩, ⟨.hall 5 26, 16765555617640429600⟩, ⟨.hall 3 27, 1088851077269455500⟩, ⟨.hall 4 27, 24322479673528436400⟩, ⟨.hall 2 29, 28866848614005402000⟩]
  caps := #[0, 8209132363940508000, 183768977742386400, 86566824506962800, 15445090941134400, 4398591507055200, 457536705225600, 2283284134731600, 0, 115928276423960, 0, 79689794276820, 0, 105396678563715, 184449773353365, 125728408554840, 973219022796930, 322129848922245, 1384667495300440, 2980747648929960, 651989804946480, 0, 0, 7003348489832614920, 0] }

theorem case_56_32_16_checked :
    (Witness.linear .positive case_56_32_16).check 56 32 16 = true := by
  change case_56_32_16.check 56 32 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_32_17 : Certificate := {
  objectiveScale := 172907280000000
  eta := 2459455501913260250400
  rows := #[⟨.count 2, 587377615276283832000⟩, ⟨.count 3, 137602448333954604000⟩, ⟨.count 4, 35520404573484230400⟩, ⟨.count 5, 9212615943893762400⟩, ⟨.count 6, 2415107498533329600⟩, ⟨.count 7, 641352076549984800⟩, ⟨.count 8, 174079259376422400⟩, ⟨.count 9, 50867316051552000⟩, ⟨.count 10, 15684089115895200⟩, ⟨.count 11, 4995897112206000⟩, ⟨.count 12, 1844638933737600⟩, ⟨.count 13, 666119614960800⟩, ⟨.count 14, 423894300429600⟩, ⟨.count 15, 635841450644400⟩, ⟨.path 14, 39295689765696⟩, ⟨.privateRow 2 30, 21085350291969163200⟩, ⟨.privateRow 4 26, 4179254649706936800⟩, ⟨.privateRow 5 23, 192467390420200896⟩, ⟨.privateRow 5 24, 1388738284536002400⟩, ⟨.privateRow 5 25, 3432074333238270720⟩, ⟨.privateRow 6 21, 124221215468750400⟩, ⟨.privateRow 6 22, 489815919779266080⟩, ⟨.privateRow 6 23, 1181302580804346000⟩, ⟨.privateRow 6 24, 2033178733846260000⟩, ⟨.privateRow 7 19, 58237886336572800⟩, ⟨.privateRow 7 20, 179411580536588400⟩, ⟨.privateRow 7 21, 417753888706234080⟩, ⟨.privateRow 7 22, 715816175325451200⟩, ⟨.privateRow 7 23, 1040438467683014400⟩, ⟨.privateRow 8 17, 24267948699594600⟩, ⟨.privateRow 8 18, 67520306425572000⟩, ⟨.privateRow 8 19, 152860994671585200⟩, ⟨.privateRow 8 20, 260355879323860320⟩, ⟨.privateRow 8 21, 374687237054730600⟩, ⟨.privateRow 8 22, 461244098234119200⟩, ⟨.privateRow 9 15, 9592571020832800⟩, ⟨.privateRow 9 16, 25963525901313000⟩, ⟨.privateRow 9 17, 58134075487488000⟩, ⟨.privateRow 9 18, 98908670100240000⟩, ⟨.privateRow 9 19, 141877422353787120⟩, ⟨.privateRow 9 20, 173196146250527400⟩, ⟨.privateRow 9 21, 169204474921482000⟩, ⟨.privateRow 10 12, 134875459227600⟩, ⟨.privateRow 10 13, 3573428952621528⟩, ⟨.privateRow 10 14, 10197012893667600⟩, ⟨.privateRow 10 15, 23043953907104130⟩, ⟨.privateRow 10 16, 39640172723030880⟩, ⟨.privateRow 10 17, 57296379608067600⟩, ⟨.privateRow 10 18, 70493622161442480⟩, ⟨.privateRow 10 19, 70302869726249160⟩, ⟨.privateRow 10 20, 8421366768534720⟩, ⟨.privateRow 11 10, 116066296546200⟩, ⟨.privateRow 11 11, 1395548118946800⟩, ⟨.privateRow 11 12, 4020940221217920⟩, ⟨.privateRow 11 13, 9537621759666000⟩, ⟨.privateRow 11 14, 16891430918011650⟩, ⟨.privateRow 11 15, 25018414629436800⟩, ⟨.privateRow 11 16, 31660867153515600⟩, ⟨.privateRow 11 17, 133223922992160⟩, ⟨.privateRow 12 8, 61093810839600⟩, ⟨.privateRow 12 9, 584989661856600⟩, ⟨.privateRow 12 10, 1669957216527600⟩, ⟨.privateRow 12 11, 4071015646818120⟩, ⟨.privateRow 12 12, 7685995557240000⟩, ⟨.privateRow 12 13, 11926103106317400⟩, ⟨.privateRow 12 14, 933299460522000⟩, ⟨.privateRow 13 6, 25619985190800⟩, ⟨.privateRow 13 7, 258170619999600⟩, ⟨.privateRow 13 8, 747249568065000⟩, ⟨.privateRow 13 9, 1851626202426000⟩, ⟨.privateRow 13 10, 3689277867475200⟩, ⟨.privateRow 13 11, 965019442186800⟩, ⟨.privateRow 14 4, 8074177151040⟩, ⟨.privateRow 14 5, 118949931243000⟩, ⟨.privateRow 14 6, 361008882234000⟩, ⟨.privateRow 14 7, 920960831290500⟩, ⟨.privateRow 14 8, 462430145923200⟩, ⟨.privateRow 15 3, 56519240057280⟩, ⟨.privateRow 15 4, 187724618761680⟩, ⟨.privateRow 15 5, 153254093232240⟩, ⟨.privateRow 16 0, 12467479424400⟩, ⟨.privateRow 16 1, 13246696888425⟩, ⟨.privateRow 16 2, 42389430042960⟩, ⟨.privateRow 17 0, 17662262517900⟩, ⟨.privateRow 18 0, 22876835261280⟩, ⟨.hall 8 23, 313352086750903200⟩, ⟨.hall 7 24, 1349577717935743296⟩, ⟨.hall 6 25, 3697732462588164000⟩, ⟨.hall 5 26, 8341847337731908000⟩, ⟨.hall 4 27, 16393817938375706400⟩, ⟨.hall 3 28, 28115374157786916000⟩, ⟨.hall 2 29, 35945501926309335360⟩, ⟨.assumptionRow 17, 226186698716160⟩]
  caps := #[0, 16765856385260018400, 0, 64830504410118720, 0, 5405844165601152, 0, 191114927976960, 0, 0, 123509268878814, 511654268026980, 0, 20354656347792, 19390376971836, 0, 916108319701575, 75043719135840, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_32_17_checked :
    (Witness.linear .conditional case_56_32_17).check 56 32 17 = true := by
  change case_56_32_17.check 56 32 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_32_18 : Certificate := {
  objectiveScale := 7481565000000
  eta := 83935913662261861200
  rows := #[⟨.count 2, 20506082426805175200⟩, ⟨.count 3, 5055428641431168000⟩, ⟨.count 4, 1339086753236232000⟩, ⟨.count 5, 358845158030158800⟩, ⟨.count 6, 97877659787107200⟩, ⟨.count 7, 27254229700698000⟩, ⟨.count 8, 7782264592502400⟩, ⟨.count 9, 2274355958074200⟩, ⟨.count 10, 701055958402800⟩, ⟨.count 11, 217769874121800⟩, ⟨.count 12, 70947651297600⟩, ⟨.count 13, 38429977786200⟩, ⟨.count 14, 16303626939600⟩, ⟨.path 13, 1575701752800⟩, ⟨.privateRow 2 30, 1390242876393571200⟩, ⟨.privateRow 4 26, 183560206623393600⟩, ⟨.privateRow 5 23, 4212857201192640⟩, ⟨.privateRow 5 24, 58491008462987100⟩, ⟨.privateRow 5 25, 157530767487453360⟩, ⟨.privateRow 6 21, 2560445792704800⟩, ⟨.privateRow 6 22, 19314208108475280⟩, ⟨.privateRow 6 23, 52908180780955500⟩, ⟨.privateRow 6 24, 100121349399271200⟩, ⟨.privateRow 7 19, 1112417538804000⟩, ⟨.privateRow 7 20, 6533096223654000⟩, ⟨.privateRow 7 21, 18115813892095920⟩, ⟨.privateRow 7 22, 34919069361075900⟩, ⟨.privateRow 7 23, 56206624480406400⟩, ⟨.privateRow 8 17, 419818393694700⟩, ⟨.privateRow 8 18, 2246018701726800⟩, ⟨.privateRow 8 19, 6345733907713200⟩, ⟨.privateRow 8 20, 12514664038836960⟩, ⟨.privateRow 8 21, 20306167353271800⟩, ⟨.privateRow 8 22, 28232447317074000⟩, ⟨.privateRow 9 15, 145223047369400⟩, ⟨.privateRow 9 16, 781215457522500⟩, ⟨.privateRow 9 17, 2279014137199800⟩, ⟨.privateRow 9 18, 4633853079055200⟩, ⟨.privateRow 9 19, 7650205214291640⟩, ⟨.privateRow 9 20, 10718276077208700⟩, ⟨.privateRow 9 21, 12349091649694800⟩, ⟨.privateRow 10 13, 46465336777860⟩, ⟨.privateRow 10 14, 273538629764400⟩, ⟨.privateRow 10 15, 839636787389400⟩, ⟨.privateRow 10 16, 1780588970760600⟩, ⟨.privateRow 10 17, 3027040068452400⟩, ⟨.privateRow 10 18, 4329591170080176⟩, ⟨.privateRow 10 19, 5171510465241120⟩, ⟨.privateRow 10 20, 4585123349646840⟩, ⟨.privateRow 11 11, 13339331132400⟩, ⟨.privateRow 11 12, 95842035509220⟩, ⟨.privateRow 11 13, 317144362134600⟩, ⟨.privateRow 11 14, 712264701923775⟩, ⟨.privateRow 11 15, 1265527450301400⟩, ⟨.privateRow 11 16, 1878022550804400⟩, ⟨.privateRow 11 17, 2344927371827040⟩, ⟨.privateRow 11 18, 1013153959818000⟩, ⟨.privateRow 12 9, 2874036800250⟩, ⟨.privateRow 12 10, 33234316453800⟩, ⟨.privateRow 12 11, 122483236892940⟩, ⟨.privateRow 12 12, 296929059134400⟩, ⟨.privateRow 12 13, 561176214083100⟩, ⟨.privateRow 12 14, 880088722048800⟩, ⟨.privateRow 12 15, 660700002708900⟩, ⟨.privateRow 13 8, 11085570515250⟩, ⟨.privateRow 13 9, 48104657508600⟩, ⟨.privateRow 13 10, 128789694786060⟩, ⟨.privateRow 13 11, 263973437158200⟩, ⟨.privateRow 13 12, 360034695734175⟩, ⟨.privateRow 14 6, 2687411034000⟩, ⟨.privateRow 14 7, 18923852697750⟩, ⟨.privateRow 14 8, 57803768240400⟩, ⟨.privateRow 14 9, 131360651341920⟩, ⟨.privateRow 14 10, 28854831805800⟩, ⟨.privateRow 15 4, 698726868840⟩, ⟨.privateRow 15 5, 6521450775840⟩, ⟨.privateRow 15 6, 26493393776850⟩, ⟨.privateRow 15 7, 30087602443080⟩, ⟨.privateRow 16 3, 2329089562800⟩, ⟨.privateRow 16 4, 12123209775600⟩, ⟨.privateRow 17 1, 1086908462640⟩, ⟨.privateRow 17 2, 1940907969000⟩, ⟨.privateRow 18 0, 879878279280⟩, ⟨.hall 8 22, 1065170293387200⟩, ⟨.hall 9 22, 4583800156735800⟩, ⟨.hall 8 23, 8231520090393600⟩, ⟨.hall 7 24, 96293350957435632⟩, ⟨.hall 6 25, 225058312006743600⟩, ⟨.hall 5 26, 458677614061066400⟩, ⟨.hall 4 27, 838809960594606000⟩, ⟨.hall 3 28, 1373899895871703200⟩, ⟨.hall 2 29, 1791868596240602880⟩, ⟨.assumptionRow 18, 7637647071600⟩]
  caps := #[0, 0, 8332373958526800, 5064400576740960, 152050365230400, 662520112909200, 134163792972300, 0, 47635600225164, 13588030415260, 3313893716364, 3560193415800, 4182562049820, 0, 6630579574710, 17196929125740, 18824807282400, 7637647071600, 0, 7481565000000, 0, 0, 0, 0, 0] }

theorem case_56_32_18_checked :
    (Witness.linear .conditional case_56_32_18).check 56 32 18 = true := by
  change case_56_32_18.check 56 32 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_32_19 : Certificate := {
  objectiveScale := 10925460000000
  eta := 113246867639559654000
  rows := #[⟨.count 2, 27225589662707436000⟩, ⟨.count 3, 6603653662869463200⟩, ⟨.count 4, 1688152064192193600⟩, ⟨.count 5, 436331638694952000⟩, ⟨.count 6, 113794657859282400⟩, ⟨.count 7, 30118233499754400⟩, ⟨.count 8, 8086598962041600⟩, ⟨.count 9, 2347722279302400⟩, ⟨.count 10, 766270466161200⟩, ⟨.count 11, 256199851908000⟩, ⟨.count 12, 94596868396800⟩, ⟨.count 13, 51239970381600⟩, ⟨.count 14, 16303626939600⟩, ⟨.count 15, 24455440409400⟩, ⟨.path 12, 3551259004160⟩, ⟨.privateRow 2 30, 2201217887623154400⟩, ⟨.privateRow 4 26, 252771432071558400⟩, ⟨.privateRow 5 23, 3701295969619248⟩, ⟨.privateRow 5 24, 77072717903961780⟩, ⟨.privateRow 5 25, 222629441858263440⟩, ⟨.privateRow 6 21, 1953329780001600⟩, ⟨.privateRow 6 22, 23923010535343920⟩, ⟨.privateRow 6 23, 72250105055228100⟩, ⟨.privateRow 6 24, 148479459628500000⟩, ⟨.privateRow 7 19, 682534150927200⟩, ⟨.privateRow 7 20, 7463567503992600⟩, ⟨.privateRow 7 21, 23677524495424800⟩, ⟨.privateRow 7 22, 50555606231730600⟩, ⟨.privateRow 7 23, 89241654475974000⟩, ⟨.privateRow 8 17, 177301942968150⟩, ⟨.privateRow 8 18, 2305798667172000⟩, ⟨.privateRow 8 19, 7834798501530000⟩, ⟨.privateRow 8 20, 17555745488561280⟩, ⟨.privateRow 8 21, 31783920718750200⟩, ⟨.privateRow 8 22, 49204346103712800⟩, ⟨.privateRow 9 15, 23247764339800⟩, ⟨.privateRow 9 16, 691885168249275⟩, ⟨.privateRow 9 17, 2607415765554600⟩, ⟨.privateRow 9 18, 6227985490927200⟩, ⟨.privateRow 9 19, 11703830325707520⟩, ⟨.privateRow 9 20, 18537903148114350⟩, ⟨.privateRow 9 21, 24762492050095800⟩, ⟨.privateRow 10 14, 183687530186160⟩, ⟨.privateRow 10 15, 865111204482525⟩, ⟨.privateRow 10 16, 2254791605746680⟩, ⟨.privateRow 10 17, 4468824144144360⟩, ⟨.privateRow 10 18, 7332067107276912⟩, ⟨.privateRow 10 19, 10131481370940930⟩, ⟨.privateRow 10 20, 11140268287828680⟩, ⟨.privateRow 11 12, 41108430783420⟩, ⟨.privateRow 11 13, 273797417493600⟩, ⟨.privateRow 11 14, 828864748161450⟩, ⟨.privateRow 11 15, 1769941704187800⟩, ⟨.privateRow 11 16, 3057900505159500⟩, ⟨.privateRow 11 17, 4429928348445600⟩, ⟨.privateRow 11 18, 5254134917481450⟩, ⟨.privateRow 11 19, 3569717936584800⟩, ⟨.privateRow 12 10, 7166429424000⟩, ⟨.privateRow 12 11, 81294183778500⟩, ⟨.privateRow 12 12, 300542133969000⟩, ⟨.privateRow 12 13, 723641408634375⟩, ⟨.privateRow 12 14, 1345753068264000⟩, ⟨.privateRow 12 15, 2078010721917900⟩, ⟨.privateRow 12 16, 2297718517996440⟩, ⟨.privateRow 13 9, 22126350846600⟩, ⟨.privateRow 13 10, 106027323328080⟩, ⟨.privateRow 13 11, 298571365877400⟩, ⟨.privateRow 13 12, 620915121859725⟩, ⟨.privateRow 13 13, 1044647857697400⟩, ⟨.privateRow 13 14, 346362492098700⟩, ⟨.privateRow 14 7, 3687725141100⟩, ⟨.privateRow 14 8, 35995020516000⟩, ⟨.privateRow 14 9, 122510111003280⟩, ⟨.privateRow 14 10, 294241648100400⟩, ⟨.privateRow 14 11, 367705014727050⟩, ⟨.privateRow 15 5, 376237544760⟩, ⟨.privateRow 15 6, 9918039721590⟩, ⟨.privateRow 15 7, 37350127170720⟩, ⟨.privateRow 15 8, 165155740898148⟩, ⟨.privateRow 15 9, 45106701199560⟩, ⟨.privateRow 16 4, 2299229440200⟩, ⟨.privateRow 16 5, 17435823254850⟩, ⟨.privateRow 16 6, 52369225927200⟩, ⟨.privateRow 17 2, 388181593800⟩, ⟨.privateRow 17 3, 6270625746000⟩, ⟨.privateRow 17 4, 10869084626400⟩, ⟨.privateRow 18 1, 1885453455600⟩, ⟨.privateRow 18 2, 1015244168400⟩, ⟨.hall 9 21, 101349918060300⟩, ⟨.hall 9 22, 20788187628007800⟩, ⟨.hall 8 23, 78625146673273200⟩, ⟨.hall 7 24, 191200893625005264⟩, ⟨.hall 6 25, 399167610666501600⟩, ⟨.hall 5 26, 752797459403589600⟩, ⟨.hall 4 27, 1302546665266704000⟩, ⟨.hall 3 28, 2057036481685785600⟩, ⟨.hall 2 29, 2668493965522104720⟩, ⟨.assumptionRow 19, 8035425256950⟩]
  caps := #[0, 0, 84172861392697350, 0, 1269981417211920, 491946466051872, 41619377215920, 0, 49102609951458, 9699684753885, 13525724587683, 13129513891860, 3298110162125, 0, 6862541115780, 0, 9780399260100, 8035425256950, 73410345050850, 123070094743050, 10925460000000, 0, 0, 0, 0] }

theorem case_56_32_19_checked :
    (Witness.linear .conditional case_56_32_19).check 56 32 19 = true := by
  change case_56_32_19.check 56 32 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_32_20 : Certificate := {
  objectiveScale := 12299364000000
  eta := 127902344628208550400
  rows := #[⟨.count 2, 31743879010986542400⟩, ⟨.count 3, 7914905466740672400⟩, ⟨.count 4, 2055272477438980800⟩, ⟨.count 5, 535634701294492800⟩, ⟨.count 6, 139927042753898400⟩, ⟨.count 7, 36492951633138000⟩, ⟨.count 8, 9477841794220800⟩, ⟨.count 9, 2421088600530600⟩, ⟨.count 10, 652145077584000⟩, ⟨.count 11, 166529903740200⟩, ⟨.count 12, 35473825648800⟩, ⟨.count 13, 12809992595400⟩, ⟨.path 12, 770060695320⟩, ⟨.path 13, 3069738102928⟩, ⟨.privateRow 2 30, 3185973258401934000⟩, ⟨.privateRow 4 26, 324239545306076400⟩, ⟨.privateRow 5 23, 3129551063743104⟩, ⟨.privateRow 5 24, 96557182459477740⟩, ⟨.privateRow 5 25, 289383167272399200⟩, ⟨.privateRow 6 21, 1649771773650000⟩, ⟨.privateRow 6 22, 29030703946564320⟩, ⟨.privateRow 6 23, 91968177293892900⟩, ⟨.privateRow 6 24, 197457884044621200⟩, ⟨.privateRow 7 19, 586376024691600⟩, ⟨.privateRow 7 20, 8719593747664800⟩, ⟨.privateRow 7 21, 29334261952915920⟩, ⟨.privateRow 7 22, 65931479162148600⟩, ⟨.privateRow 7 23, 122606638826271600⟩, ⟨.privateRow 8 17, 162356951606850⟩, ⟨.privateRow 8 18, 2586842141083200⟩, ⟨.privateRow 8 19, 9378208518478800⟩, ⟨.privateRow 8 20, 22307709287223360⟩, ⟨.privateRow 8 21, 42888049300196100⟩, ⟨.privateRow 8 22, 70783102115325600⟩, ⟨.privateRow 9 15, 31701496827000⟩, ⟨.privateRow 9 16, 745890932486700⟩, ⟨.privateRow 9 17, 2990550998635200⟩, ⟨.privateRow 9 18, 7645948156146300⟩, ⟨.privateRow 9 19, 15397145281758240⟩, ⟨.privateRow 9 20, 26227101203503200⟩, ⟨.privateRow 9 21, 38039078921243400⟩, ⟨.privateRow 10 14, 203070731103240⟩, ⟨.privateRow 10 15, 942349637108880⟩, ⟨.privateRow 10 16, 2647941923947320⟩, ⟨.privateRow 10 17, 5679368444409660⟩, ⟨.privateRow 10 18, 10109552992707168⟩, ⟨.privateRow 10 19, 15275683261058220⟩, ⟨.privateRow 10 20, 18818189667917640⟩, ⟨.privateRow 11 12, 44485610649480⟩, ⟨.privateRow 11 13, 287771954870400⟩, ⟨.privateRow 11 14, 920135945403675⟩, ⟨.privateRow 11 15, 2149583302924200⟩, ⟨.privateRow 11 16, 4065231741070500⟩, ⟨.privateRow 11 17, 6473704439802600⟩, ⟨.privateRow 11 18, 8586479809457550⟩, ⟨.privateRow 11 19, 8494965998719200⟩, ⟨.privateRow 12 10, 8510134941000⟩, ⟨.privateRow 12 11, 78338031641100⟩, ⟨.privateRow 12 12, 315979817353200⟩, ⟨.privateRow 12 13, 830062885580775⟩, ⟨.privateRow 12 14, 1704573630084600⟩, ⟨.privateRow 12 15, 2905076397692700⟩, ⟨.privateRow 12 16, 4164035900741640⟩, ⟨.privateRow 12 17, 3363854786349750⟩, ⟨.privateRow 13 8, 492692022900⟩, ⟨.privateRow 13 9, 19259779077000⟩, ⟨.privateRow 13 10, 101001864694500⟩, ⟨.privateRow 13 11, 322330070092800⟩, ⟨.privateRow 13 12, 741255148453050⟩, ⟨.privateRow 13 13, 1379537664120000⟩, ⟨.privateRow 13 14, 2158319521650600⟩, ⟨.privateRow 13 15, 316702432320120⟩, ⟨.privateRow 14 7, 2329089562800⟩, ⟨.privateRow 14 8, 30066428901600⟩, ⟨.privateRow 14 9, 119948112484200⟩, ⟨.privateRow 14 10, 329048597677800⟩, ⟨.privateRow 14 11, 688682670100425⟩, ⟨.privateRow 14 12, 703218684425400⟩, ⟨.privateRow 15 6, 5570405871030⟩, ⟨.privateRow 15 7, 42389430042960⟩, ⟨.privateRow 15 8, 143145844529688⟩, ⟨.privateRow 15 9, 354694461641520⟩, ⟨.privateRow 15 10, 110049481842300⟩, ⟨.privateRow 16 5, 10642645363350⟩, ⟨.privateRow 16 6, 60026990095800⟩, ⟨.privateRow 16 7, 142928462837160⟩, ⟨.privateRow 17 3, 836083432800⟩, ⟨.privateRow 17 4, 19020898096200⟩, ⟨.privateRow 17 5, 43970387806800⟩, ⟨.privateRow 18 2, 2030488336800⟩, ⟨.privateRow 18 3, 14298022038300⟩, ⟨.privateRow 19 1, 3045732505200⟩, ⟨.hall 9 21, 445707651097800⟩, ⟨.hall 10 21, 7737553130743800⟩, ⟨.hall 9 22, 39556143222195600⟩, ⟨.hall 8 23, 135408867789795600⟩, ⟨.hall 7 24, 299079601885720656⟩, ⟨.hall 6 25, 588197952869234400⟩, ⟨.hall 5 26, 1064359425169040000⟩, ⟨.hall 4 27, 1788422364414457200⟩, ⟨.hall 3 28, 2770679964474021600⟩, ⟨.hall 2 29, 3595322549784485520⟩, ⟨.assumptionRow 20, 3850569122400⟩]
  caps := #[0, 301218730727514600, 0, 4103214382993880, 1161034558098800, 1175782083995376, 23046470881920, 45466823757520, 0, 8905615675880, 11794667645992, 10997676207450, 4508759726744, 8973214167568, 8173116289800, 24535486947972, 7888164946200, 3850569122400, 12877330273500, 55779086840400, 131442434877600, 12299364000000, 0, 0, 0] }

theorem case_56_32_20_checked :
    (Witness.linear .conditional case_56_32_20).check 56 32 20 = true := by
  change case_56_32_20.check 56 32 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_33_1_checked :
    (Witness.rising).check 56 33 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_33_2_checked :
    (Witness.rising).check 56 33 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_33_3_checked :
    (Witness.rising).check 56 33 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_33_4_checked :
    (Witness.rising).check 56 33 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_33_5_checked :
    (Witness.rising).check 56 33 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_33_6_checked :
    (Witness.rising).check 56 33 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_33_7_checked :
    (Witness.rising).check 56 33 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_33_8_checked :
    (Witness.rising).check 56 33 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_33_9_checked :
    (Witness.rising).check 56 33 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_33_10_checked :
    (Witness.rising).check 56 33 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_33_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_33_11_checked :
    (Witness.linear .positive case_56_33_11).check 56 33 11 = true := by
  change case_56_33_11.check 56 33 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_33_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_33_12_checked :
    (Witness.linear .positive case_56_33_12).check 56 33 12 = true := by
  change case_56_33_12.check 56 33 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_33_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_33_13_checked :
    (Witness.linear .positive case_56_33_13).check 56 33 13 = true := by
  change case_56_33_13.check 56 33 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_33_14 : Certificate := {
  objectiveScale := 927407936000000
  eta := 19898546289821184585600
  rows := #[⟨.count 2, 3775646880852867820800⟩, ⟨.count 3, 711190479235620384000⟩, ⟨.count 4, 142660585240729395840⟩, ⟨.count 5, 28351261939304304000⟩, ⟨.count 6, 5645545405778678400⟩, ⟨.count 7, 1185208464001161600⟩, ⟨.count 8, 256879946060337600⟩, ⟨.count 9, 57988740298769280⟩, ⟨.count 10, 14170180900075200⟩, ⟨.count 11, 3689277867475200⟩, ⟨.count 12, 922319466868800⟩, ⟨.count 13, 1090013915390400⟩, ⟨.path 14, 381872737655136⟩, ⟨.privateRow 3 30, 106326497390671958400⟩, ⟨.privateRow 6 25, 10277418241130040000⟩, ⟨.privateRow 7 19, 145335188718720000⟩, ⟨.privateRow 7 20, 227864813741136000⟩, ⟨.privateRow 7 21, 398097304432027200⟩, ⟨.privateRow 7 22, 633661422813619200⟩, ⟨.privateRow 7 23, 984100896611632800⟩, ⟨.privateRow 8 16, 19870045332637500⟩, ⟨.privateRow 8 17, 61605971662435200⟩, ⟨.privateRow 8 18, 123591681969005250⟩, ⟨.privateRow 8 19, 185938207067012400⟩, ⟨.privateRow 8 20, 321099932575422000⟩, ⟨.privateRow 8 21, 445788441046788840⟩, ⟨.privateRow 8 22, 632503283028516900⟩, ⟨.privateRow 8 24, 1781468784342947700⟩, ⟨.privateRow 9 13, 2599885042634880⟩, ⟨.privateRow 9 14, 12285227543359680⟩, ⟨.privateRow 9 15, 27332704491700608⟩, ⟨.privateRow 9 17, 179498041516914120⟩, ⟨.privateRow 9 18, 76615866986218560⟩, ⟨.privateRow 9 19, 175096605697453440⟩, ⟨.privateRow 9 20, 212557558007418624⟩, ⟨.privateRow 9 21, 237550365960747840⟩, ⟨.privateRow 10 10, 233574410440800⟩, ⟨.privateRow 10 11, 2439954225989280⟩, ⟨.privateRow 10 12, 6158578621955760⟩, ⟨.privateRow 10 13, 12495523157339040⟩, ⟨.privateRow 10 14, 17701825985940096⟩, ⟨.privateRow 10 15, 8211438162607680⟩, ⟨.privateRow 10 16, 113647575853391580⟩, ⟨.privateRow 10 17, 53410681854129600⟩, ⟨.privateRow 10 18, 102152470770670320⟩, ⟨.privateRow 10 19, 135030923838562752⟩, ⟨.privateRow 11 8, 441595381106880⟩, ⟨.privateRow 11 9, 1425402812433600⟩, ⟨.privateRow 11 10, 3224893240800000⟩, ⟨.privateRow 11 11, 5939178385140000⟩, ⟨.privateRow 11 12, 9611940890260800⟩, ⟨.privateRow 11 13, 12811855867050240⟩, ⟨.privateRow 11 14, 8030700812534400⟩, ⟨.privateRow 11 15, 72758428852309200⟩, ⟨.privateRow 11 16, 40833598215009600⟩, ⟨.privateRow 11 17, 59252038477632000⟩, ⟨.privateRow 11 18, 79990251944803200⟩, ⟨.privateRow 11 20, 79123830627441600⟩, ⟨.privateRow 12 7, 1726787001859920⟩, ⟨.privateRow 12 9, 5740847450830800⟩, ⟨.privateRow 12 10, 3804567800833800⟩, ⟨.privateRow 12 12, 2344228644958200⟩, ⟨.privateRow 12 13, 46756472973210000⟩, ⟨.privateRow 12 14, 25767300105647100⟩, ⟨.privateRow 12 16, 113458104417457800⟩, ⟨.privateRow 12 21, 378535281194070000⟩, ⟨.privateRow 13 4, 192355396833600⟩, ⟨.privateRow 13 5, 597411472858200⟩, ⟨.privateRow 13 6, 1145912064897600⟩, ⟨.privateRow 13 7, 1090013915390400⟩, ⟨.privateRow 13 8, 5075981961019200⟩, ⟨.privateRow 13 9, 3479659806823200⟩, ⟨.privateRow 13 11, 2096180606520000⟩, ⟨.privateRow 13 12, 38383395994944000⟩, ⟨.privateRow 13 13, 27093134339271000⟩, ⟨.privateRow 13 14, 6791625165124800⟩, ⟨.privateRow 13 15, 61543862607427200⟩, ⟨.privateRow 13 16, 49453092869019840⟩, ⟨.privateRow 14 2, 260392213121040⟩, ⟨.privateRow 14 3, 262885709005920⟩, ⟨.privateRow 14 4, 824323023513990⟩, ⟨.privateRow 14 6, 4103123810076720⟩, ⟨.privateRow 14 8, 10727553617300520⟩, ⟨.privateRow 14 11, 35025780481211520⟩, ⟨.privateRow 14 13, 22781290831659360⟩, ⟨.privateRow 14 14, 123880081484118960⟩, ⟨.privateRow 15 0, 205254082313280⟩, ⟨.privateRow 15 1, 292016073629280⟩, ⟨.privateRow 15 2, 538595111134080⟩, ⟨.privateRow 15 3, 911372745923640⟩, ⟨.privateRow 15 4, 452153920458240⟩, ⟨.privateRow 15 5, 5462180842678560⟩, ⟨.privateRow 15 7, 14299367734491840⟩, ⟨.privateRow 15 8, 1186904041202880⟩, ⟨.privateRow 15 10, 35023089088827840⟩, ⟨.privateRow 15 11, 15556920825766320⟩, ⟨.privateRow 15 12, 17706670492230720⟩, ⟨.privateRow 15 13, 97778285299094400⟩, ⟨.privateRow 15 16, 160571161002732480⟩, ⟨.privateRow 16 0, 1695577201718400⟩, ⟨.privateRow 16 1, 336621944458800⟩, ⟨.privateRow 16 2, 1430643263949900⟩, ⟨.privateRow 16 3, 741815025751800⟩, ⟨.privateRow 16 4, 9560330382903300⟩, ⟨.privateRow 16 6, 21459648959248500⟩, ⟨.privateRow 16 7, 5202339141636000⟩, ⟨.privateRow 16 8, 445089015451080⟩, ⟨.privateRow 16 9, 39422169939952800⟩, ⟨.privateRow 16 10, 37474905497354325⟩, ⟨.privateRow 16 13, 75410796046425840⟩, ⟨.privateRow 17 0, 8249909241974400⟩, ⟨.privateRow 17 2, 775121006499840⟩, ⟨.privateRow 17 4, 39631788000604800⟩, ⟨.privateRow 17 5, 17621891632144800⟩, ⟨.privateRow 17 6, 17374161196828800⟩, ⟨.privateRow 17 8, 58214817258998400⟩, ⟨.privateRow 17 10, 129659750506915200⟩, ⟨.privateRow 17 11, 34759332635227200⟩, ⟨.privateRow 17 13, 107729708637751200⟩, ⟨.privateRow 18 0, 31141091999417400⟩, ⟨.privateRow 18 4, 76351437684522000⟩, ⟨.privateRow 18 7, 411325497997814400⟩, ⟨.privateRow 18 10, 212754567929904000⟩, ⟨.privateRow 19 1, 208068084820664640⟩, ⟨.privateRow 19 3, 80915366319147360⟩, ⟨.privateRow 19 5, 152689149267887232⟩, ⟨.privateRow 19 6, 664617818010706560⟩, ⟨.privateRow 19 8, 1126638382947517440⟩, ⟨.privateRow 20 0, 729297167532991200⟩, ⟨.privateRow 20 1, 208536431459035680⟩, ⟨.privateRow 20 2, 240584238025251120⟩, ⟨.privateRow 20 3, 121625734522743360⟩, ⟨.privateRow 20 4, 380240454244787136⟩, ⟨.privateRow 20 5, 1799491861652284800⟩, ⟨.privateRow 20 6, 1496316602352171600⟩, ⟨.privateRow 20 10, 10456612491731646240⟩, ⟨.privateRow 21 0, 7908134803381612800⟩, ⟨.privateRow 21 3, 1596071042508983040⟩, ⟨.privateRow 21 5, 22268711787947024400⟩, ⟨.privateRow 21 12, 211479413132440252800⟩, ⟨.hall 12 6, 394018911000⟩, ⟨.hall 17 7, 129762048960180⟩, ⟨.hall 18 8, 661156536837888⟩, ⟨.hall 13 10, 1089683529480⟩, ⟨.hall 14 10, 1695981006720⟩, ⟨.hall 21 11, 484278467420096949600⟩, ⟨.hall 8 14, 1042475281848⟩, ⟨.hall 15 16, 1828563648912000⟩, ⟨.hall 16 16, 29323511606188800⟩, ⟨.hall 12 20, 17524069870507200⟩, ⟨.hall 5 22, 322674864866640⟩, ⟨.hall 9 23, 1280203176727434960⟩, ⟨.hall 7 24, 21559916264927040⟩, ⟨.hall 6 25, 48076549179859200⟩, ⟨.hall 4 28, 74105610878358259200⟩, ⟨.hall 3 29, 91821028210222671360⟩]
  caps := #[0, 0, 0, 62485649185173760, 37655270840066880, 20213318013002400, 0, 946927581809664, 4454800005786130, 0, 0, 2172218416006240, 386961206786336, 1071792079012176, 92115442922776, 859841211432840, 4479147750597975, 4761902908133280, 629112969685200, 10344351838803840, 0, 81247960308715200, 0, 0] }

theorem case_56_33_14_checked :
    (Witness.linear .positive case_56_33_14).check 56 33 14 = true := by
  change case_56_33_14.check 56 33 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_33_15 : Certificate := {
  objectiveScale := 166933428480000
  eta := 5458093532721160531200
  rows := #[⟨.count 2, 1184613316403358441600⟩, ⟨.count 3, 250677040205822630400⟩, ⟨.count 4, 56238032615463578880⟩, ⟨.count 5, 11995239800899555200⟩, ⟨.count 6, 2804242466327702400⟩, ⟨.count 7, 630754719039244800⟩, ⟨.count 8, 150906370952937600⟩, ⟨.count 9, 36624467557117440⟩, ⟨.count 10, 9446787266716800⟩, ⟨.count 11, 2459518578316800⟩, ⟨.count 12, 922319466868800⟩, ⟨.count 13, 363337971796800⟩, ⟨.path 14, 74191773715488⟩, ⟨.privateRow 2 31, 18073157393116425600⟩, ⟨.privateRow 3 30, 76439284731925315200⟩, ⟨.privateRow 6 25, 5950951156516766400⟩, ⟨.privateRow 7 19, 27462295034974800⟩, ⟨.privateRow 7 20, 109693463866272000⟩, ⟨.privateRow 7 21, 208757850240139200⟩, ⟨.privateRow 7 22, 353552069089739520⟩, ⟨.privateRow 7 24, 2663509558585075200⟩, ⟨.privateRow 8 17, 19828833386762400⟩, ⟨.privateRow 8 19, 198034333711414200⟩, ⟨.privateRow 8 20, 136811885463653400⟩, ⟨.privateRow 9 14, 1238285168527680⟩, ⟨.privateRow 9 15, 8833957220952864⟩, ⟨.privateRow 9 16, 18086156818329600⟩, ⟨.privateRow 9 17, 19357839719618400⟩, ⟨.privateRow 9 18, 123026237250396480⟩, ⟨.privateRow 9 19, 100886843502244800⟩, ⟨.privateRow 9 20, 76154024053179072⟩, ⟨.privateRow 9 21, 94005626025270960⟩, ⟨.privateRow 9 23, 401795277567203520⟩, ⟨.privateRow 10 12, 1183876224771240⟩, ⟨.privateRow 10 13, 3818351776337280⟩, ⟨.privateRow 10 14, 8672877386789616⟩, ⟨.privateRow 10 15, 14674816972015200⟩, ⟨.privateRow 10 16, 19325038374942300⟩, ⟨.privateRow 10 17, 72880406599983840⟩, ⟨.privateRow 10 18, 66351569282958960⟩, ⟨.privateRow 10 19, 57036794812661664⟩, ⟨.privateRow 11 9, 59890874472000⟩, ⟨.privateRow 11 10, 683677367049600⟩, ⟨.privateRow 11 11, 1839980754612000⟩, ⟨.privateRow 11 12, 3821400766310400⟩, ⟨.privateRow 11 13, 6936960353843520⟩, ⟨.privateRow 11 14, 12384545568595200⟩, ⟨.privateRow 11 15, 14868907768915200⟩, ⟨.privateRow 11 16, 44578774231992000⟩, ⟨.privateRow 11 17, 23379401031386400⟩, ⟨.privateRow 11 18, 89263754948047680⟩, ⟨.privateRow 12 7, 85399950636000⟩, ⟨.privateRow 12 8, 353189795844600⟩, ⟨.privateRow 12 9, 934144075418400⟩, ⟨.privateRow 12 10, 1857448926333000⟩, ⟨.privateRow 12 11, 3256067208794400⟩, ⟨.privateRow 12 12, 6197474417654520⟩, ⟨.privateRow 12 13, 9584721126380400⟩, ⟨.privateRow 12 14, 10789216263475650⟩, ⟨.privateRow 12 15, 27219404266282800⟩, ⟨.privateRow 12 16, 19351628814117600⟩, ⟨.privateRow 12 17, 37640882242323360⟩, ⟨.privateRow 13 5, 76859955572400⟩, ⟨.privateRow 13 6, 201233338225920⟩, ⟨.privateRow 13 7, 495097895635200⟩, ⟨.privateRow 13 8, 1016916335265600⟩, ⟨.privateRow 13 9, 1788740784230400⟩, ⟨.privateRow 13 10, 3379297220208000⟩, ⟨.privateRow 13 11, 5802227918847360⟩, ⟨.privateRow 13 12, 8689056795619200⟩, ⟨.privateRow 13 13, 10162982307277800⟩, ⟨.privateRow 13 15, 66197383553901600⟩, ⟨.privateRow 13 16, 9994589131887360⟩, ⟨.privateRow 13 19, 179013823796808000⟩, ⟨.privateRow 14 3, 66255747798240⟩, ⟨.privateRow 14 4, 129439152452610⟩, ⟨.privateRow 14 5, 295514883728064⟩, ⟨.privateRow 14 6, 612484009600320⟩, ⟨.privateRow 14 7, 1134732434996160⟩, ⟨.privateRow 14 8, 2164888748622600⟩, ⟨.privateRow 14 10, 2866736597476752⟩, ⟨.privateRow 14 11, 26773971432848640⟩, ⟨.privateRow 14 13, 4084956911486880⟩, ⟨.privateRow 14 14, 39737062848843360⟩, ⟨.privateRow 14 16, 6176745520545600⟩, ⟨.privateRow 15 2, 222752299049280⟩, ⟨.privateRow 15 3, 141298100143200⟩, ⟨.privateRow 15 4, 429546224435328⟩, ⟨.privateRow 15 5, 819528980830560⟩, ⟨.privateRow 15 6, 1639057961661120⟩, ⟨.privateRow 15 7, 113038480114560⟩, ⟨.privateRow 15 9, 11982078892143360⟩, ⟨.privateRow 15 10, 18770667614578880⟩, ⟨.privateRow 15 11, 18248649633494280⟩, ⟨.privateRow 15 13, 29211027236270880⟩, ⟨.privateRow 15 14, 30904720463320704⟩, ⟨.privateRow 16 0, 105973575107400⟩, ⟨.privateRow 16 1, 292985766473400⟩, ⟨.privateRow 16 2, 238440543991650⟩, ⟨.privateRow 16 3, 671165975680200⟩, ⟨.privateRow 16 4, 1400365099633500⟩, ⟨.privateRow 16 5, 2633035750745400⟩, ⟨.privateRow 16 6, 344414119099050⟩, ⟨.privateRow 16 8, 14952871447654140⟩, ⟨.privateRow 16 9, 27082135860780000⟩, ⟨.privateRow 16 10, 29950781664728925⟩, ⟨.privateRow 16 11, 13655452106696400⟩, ⟨.privateRow 16 13, 92239399773480960⟩, ⟨.privateRow 17 0, 1239623668483200⟩, ⟨.privateRow 17 1, 196808068056600⟩, ⟨.privateRow 17 2, 1501796950093440⟩, ⟨.privateRow 17 4, 1956435232752000⟩, ⟨.privateRow 17 5, 12070894840804800⟩, ⟨.privateRow 17 7, 17052662142996480⟩, ⟨.privateRow 17 8, 1883974668576000⟩, ⟨.privateRow 17 9, 144881016253974000⟩, ⟨.privateRow 17 12, 97277686315729920⟩, ⟨.privateRow 17 14, 181265277040848000⟩, ⟨.privateRow 18 0, 7334885305647900⟩, ⟨.privateRow 18 3, 3959452256760000⟩, ⟨.privateRow 18 5, 17968714241587200⟩, ⟨.privateRow 18 7, 144962879438977600⟩, ⟨.privateRow 18 8, 112639817617727400⟩, ⟨.privateRow 19 0, 37060473123273600⟩, ⟨.privateRow 19 3, 4117830347030400⟩, ⟨.privateRow 19 5, 103522254924344256⟩, ⟨.privateRow 19 7, 842508089002419840⟩, ⟨.privateRow 20 1, 278951330393255520⟩, ⟨.privateRow 20 4, 164301430846512960⟩, ⟨.privateRow 20 5, 207332757972980640⟩, ⟨.privateRow 20 6, 1685556643237887420⟩, ⟨.privateRow 20 7, 2105740787175717120⟩, ⟨.privateRow 21 0, 1209691853485315200⟩, ⟨.privateRow 21 3, 2221981255257603840⟩, ⟨.privateRow 21 5, 5183318949324516000⟩, ⟨.privateRow 21 6, 11087552340118425600⟩, ⟨.privateRow 21 12, 50542249679451129600⟩, ⟨.privateRow 22 1, 27632513369640816000⟩, ⟨.privateRow 22 7, 234622443248820506880⟩, ⟨.hall 15 2, 28398147577800⟩, ⟨.hall 17 2, 251645187874080⟩, ⟨.hall 11 10, 769059937800⟩, ⟨.hall 9 14, 528940660248⟩, ⟨.hall 10 14, 740191364640⟩, ⟨.hall 15 14, 50701082992560⟩, ⟨.hall 11 17, 4957049766240⟩, ⟨.hall 14 18, 13975125778373760⟩, ⟨.hall 6 20, 34488976271360⟩, ⟨.hall 8 20, 10416645937152⟩, ⟨.hall 10 22, 74342108490249600⟩, ⟨.hall 5 23, 865448275499808⟩, ⟨.hall 9 23, 184457604831940440⟩, ⟨.hall 7 24, 845180020548864⟩, ⟨.hall 4 28, 41876630699500396800⟩, ⟨.hall 3 29, 53124129307039190400⟩]
  caps := #[0, 6892808861678594400, 48502570244899680, 101879757572935680, 0, 0, 0, 496566909805824, 1347895417015056, 177755896543680, 0, 524680209501120, 0, 0, 241125202195488, 97377135317280, 1960321805817375, 0, 7354595912252680, 0, 19860612519908160, 118647815053996800, 0, 0] }

theorem case_56_33_15_checked :
    (Witness.linear .positive case_56_33_15).check 56 33 15 = true := by
  change case_56_33_15.check 56 33 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_33_16 : Certificate := {
  objectiveScale := 108532569600000
  eta := 3488119376871470140800
  rows := #[⟨.count 2, 788646868063262208000⟩, ⟨.count 3, 193406255739323827200⟩, ⟨.count 4, 46990209222102706560⟩, ⟨.count 5, 11266383829475174400⟩, ⟨.count 6, 2680707555916790400⟩, ⟨.count 7, 690099921099388800⟩, ⟨.count 8, 177187817579572800⟩, ⟨.count 9, 45780584446396800⟩, ⟨.count 10, 11990153069294400⟩, ⟨.count 11, 3381838045185600⟩, ⟨.count 12, 922319466868800⟩, ⟨.count 13, 363337971796800⟩, ⟨.path 14, 35481700223424⟩, ⟨.privateRow 2 31, 63256050875907489600⟩, ⟨.privateRow 4 28, 30671556394097258640⟩, ⟨.privateRow 7 20, 108274715595446400⟩, ⟨.privateRow 7 21, 224865833656464000⟩, ⟨.privateRow 7 22, 427963685713724160⟩, ⟨.privateRow 7 25, 2509817596515028800⟩, ⟨.privateRow 8 17, 5534175588942000⟩, ⟨.privateRow 8 19, 186816273832188000⟩, ⟨.privateRow 8 20, 175368604540229100⟩, ⟨.privateRow 8 21, 364125204069026400⟩, ⟨.privateRow 8 22, 421536388383460350⟩, ⟨.privateRow 9 15, 3978954500032512⟩, ⟨.privateRow 9 16, 13099903862165120⟩, ⟨.privateRow 9 17, 22035438717332040⟩, ⟨.privateRow 9 18, 126320501528020800⟩, ⟨.privateRow 9 20, 506548037089366272⟩, ⟨.privateRow 9 21, 182528885764985760⟩, ⟨.privateRow 9 23, 956559878349435360⟩, ⟨.privateRow 10 13, 2080935656654400⟩, ⟨.privateRow 10 14, 6351147747008064⟩, ⟨.privateRow 10 16, 50912733298026600⟩, ⟨.privateRow 10 17, 68105107542083040⟩, ⟨.privateRow 10 18, 36818247808742400⟩, ⟨.privateRow 11 10, 23649217099200⟩, ⟨.privateRow 11 11, 947939452059600⟩, ⟨.privateRow 11 12, 2835560675001600⟩, ⟨.privateRow 11 13, 6009051072024000⟩, ⟨.privateRow 11 14, 3297990820924800⟩, ⟨.privateRow 11 15, 36152128193781600⟩, ⟨.privateRow 11 16, 47154081834288000⟩, ⟨.privateRow 11 17, 35672335743844800⟩, ⟨.privateRow 11 18, 17484941165852160⟩, ⟨.privateRow 12 8, 49409971439400⟩, ⟨.privateRow 12 9, 402036690686400⟩, ⟨.privateRow 12 10, 1276729262008200⟩, ⟨.privateRow 12 11, 2773945669294800⟩, ⟨.privateRow 12 13, 15759137557363200⟩, ⟨.privateRow 12 14, 20223775809987750⟩, ⟨.privateRow 12 15, 35860659271351200⟩, ⟨.privateRow 12 16, 32451981241680000⟩, ⟨.privateRow 12 17, 22320131098224960⟩, ⟨.privateRow 13 6, 42855247955520⟩, ⟨.privateRow 13 7, 193647160792800⟩, ⟨.privateRow 13 8, 578330854516800⟩, ⟨.privateRow 13 9, 1353201035986800⟩, ⟨.privateRow 13 10, 3038826673209600⟩, ⟨.privateRow 13 11, 343773619469280⟩, ⟨.privateRow 13 12, 13331708657467200⟩, ⟨.privateRow 13 13, 18135455880742200⟩, ⟨.privateRow 13 14, 29110957718356800⟩, ⟨.privateRow 13 15, 31978399697244000⟩, ⟨.privateRow 13 16, 27222398810006400⟩, ⟨.privateRow 13 18, 44187487185441600⟩, ⟨.privateRow 14 4, 31792072532220⟩, ⟨.privateRow 14 5, 111423644684352⟩, ⟨.privateRow 14 6, 295860919891680⟩, ⟨.privateRow 14 7, 690342146413920⟩, ⟨.privateRow 14 8, 1689521568855120⟩, ⟨.privateRow 14 9, 3418680007360800⟩, ⟨.privateRow 14 10, 733942703029536⟩, ⟨.privateRow 14 11, 12163747878041760⟩, ⟨.privateRow 14 12, 18616529329938540⟩, ⟨.privateRow 14 13, 27748639960367040⟩, ⟨.privateRow 14 14, 33857043338598480⟩, ⟨.privateRow 14 16, 69660972642741480⟩, ⟨.privateRow 15 2, 23272628258880⟩, ⟨.privateRow 15 3, 70649050071600⟩, ⟨.privateRow 15 4, 180861568183296⟩, ⟨.privateRow 15 5, 407745946127520⟩, ⟨.privateRow 15 6, 1008651053329920⟩, ⟨.privateRow 15 7, 2265479538962640⟩, ⟨.privateRow 15 8, 4377672048072960⟩, ⟨.privateRow 15 9, 1588190645609568⟩, ⟨.privateRow 15 10, 5149530760774400⟩, ⟨.privateRow 15 11, 36511429077002880⟩, ⟨.privateRow 15 12, 24666611196427200⟩, ⟨.privateRow 15 15, 156770242108880400⟩, ⟨.privateRow 15 17, 106312690547743680⟩, ⟨.privateRow 16 1, 93506095683000⟩, ⟨.privateRow 16 2, 105973575107400⟩, ⟨.privateRow 16 3, 289661105293560⟩, ⟨.privateRow 16 4, 711536861435400⟩, ⟨.privateRow 16 5, 1638514507429800⟩, ⟨.privateRow 16 6, 3523621372321050⟩, ⟨.privateRow 16 8, 16796811654522900⟩, ⟨.privateRow 16 10, 39726843968386575⟩, ⟨.privateRow 16 12, 95022972346302000⟩, ⟨.privateRow 16 14, 53914056335889750⟩, ⟨.privateRow 16 16, 418489648099122600⟩, ⟨.privateRow 17 0, 256473862444800⟩, ⟨.privateRow 17 1, 166529903740200⟩, ⟨.privateRow 17 2, 629785817781120⟩, ⟨.privateRow 17 3, 1418748270825600⟩, ⟨.privateRow 17 4, 3148929088905600⟩, ⟨.privateRow 17 5, 6398785392199200⟩, ⟨.privateRow 17 6, 968901258124800⟩, ⟨.privateRow 17 7, 22405841594136000⟩, ⟨.privateRow 17 8, 8262574617897600⟩, ⟨.privateRow 17 9, 37968818052765600⟩, ⟨.privateRow 17 10, 26333352051177600⟩, ⟨.privateRow 17 11, 59143347631368000⟩, ⟨.privateRow 17 14, 156719778501686400⟩, ⟨.privateRow 17 16, 562447180341446400⟩, ⟨.privateRow 18 1, 823566069406080⟩, ⟨.privateRow 18 2, 3431525289192000⟩, ⟨.privateRow 18 3, 7285392152438400⟩, ⟨.privateRow 18 4, 14412406214606400⟩, ⟨.privateRow 18 5, 6363919627228800⟩, ⟨.privateRow 18 6, 39668432343059520⟩, ⟨.privateRow 18 7, 39348156649401600⟩, ⟨.privateRow 18 9, 242853946895102400⟩, ⟨.privateRow 18 10, 61767455205456000⟩, ⟨.privateRow 18 13, 703005147579134400⟩, ⟨.privateRow 19 1, 28413029394509760⟩, ⟨.privateRow 19 2, 11783329916117760⟩, ⟨.privateRow 19 4, 109159939017642240⟩, ⟨.privateRow 19 5, 46449126314502912⟩, ⟨.privateRow 19 7, 315631696099880160⟩, ⟨.privateRow 20 0, 99754440156811440⟩, ⟨.privateRow 20 2, 148653675527797440⟩, ⟨.privateRow 20 3, 233649437372638560⟩, ⟨.privateRow 20 4, 307478392012759968⟩, ⟨.privateRow 20 5, 92582552302400160⟩, ⟨.privateRow 20 6, 630800136285719400⟩, ⟨.privateRow 20 7, 787976249978174400⟩, ⟨.privateRow 21 0, 1095342872310086400⟩, ⟨.privateRow 21 1, 130397960989296000⟩, ⟨.privateRow 21 3, 4052768627547319680⟩, ⟨.privateRow 21 7, 4277053120448908800⟩, ⟨.privateRow 22 4, 95808271862372869800⟩, ⟨.hall 17 1, 1887338909055600⟩, ⟨.hall 16 6, 106296516097200⟩, ⟨.hall 20 8, 29787879200352000⟩, ⟨.hall 17 9, 115184065651200⟩, ⟨.hall 21 9, 694546957669350240⟩, ⟨.hall 10 12, 293814799200⟩, ⟨.hall 11 12, 441348724080⟩, ⟨.hall 13 15, 28131508084680⟩, ⟨.hall 12 17, 3544419003840⟩, ⟨.hall 14 18, 19463441457620160⟩, ⟨.hall 11 19, 610620737950080⟩, ⟨.hall 12 19, 4981989120245280⟩, ⟨.hall 9 20, 322947139951800⟩, ⟨.hall 6 21, 209543186099520⟩, ⟨.hall 10 22, 856024261553260800⟩, ⟨.hall 9 23, 1459574049954220200⟩, ⟨.hall 8 24, 98106096891426624⟩, ⟨.hall 3 27, 70260733857188160⟩, ⟨.hall 5 27, 33140886894378806400⟩, ⟨.hall 4 28, 51077510826905122560⟩, ⟨.hall 2 30, 72292629572465702400⟩]
  caps := #[0, 0, 600127614759254400, 127217582133445440, 28808847578936880, 2727859154791680, 1195410281345280, 444762942912288, 398092038664320, 0, 703416137563152, 139967903871360, 152568884482560, 241706152235952, 605815913418768, 108532569600000, 34510064294160, 10123842076782720, 0, 21008517720843744, 294481779654157992, 0, 0, 0] }

theorem case_56_33_16_checked :
    (Witness.linear .positive case_56_33_16).check 56 33 16 = true := by
  change case_56_33_16.check 56 33 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_33_17 : Certificate := {
  objectiveScale := 4288100544000000
  eta := 154633934655504137433600
  rows := #[⟨.count 2, 33412338976946875545600⟩, ⟨.count 3, 7509044822345203737600⟩, ⟨.count 4, 1737558046100808771840⟩, ⟨.count 5, 391383303163851398400⟩, ⟨.count 6, 97781999420583878400⟩, ⟨.count 7, 24494308256024006400⟩, ⟨.count 8, 6149858510632636800⟩, ⟨.count 9, 1608424533550074240⟩, ⟨.count 10, 450539085028032000⟩, ⟨.count 11, 133428882873686400⟩, ⟨.count 12, 38122537963910400⟩, ⟨.count 13, 22526954251401600⟩, ⟨.path 13, 2167805451452160⟩, ⟨.privateRow 2 31, 916801984123542316800⟩, ⟨.privateRow 4 26, 34380074404632836880⟩, ⟨.privateRow 4 27, 227260174371364854720⟩, ⟨.privateRow 5 24, 27848721923752713984⟩, ⟨.privateRow 5 25, 79234056188454847680⟩, ⟨.privateRow 5 26, 173454544141892133120⟩, ⟨.privateRow 6 22, 13807771458650769600⟩, ⟨.privateRow 6 23, 29368640557043948160⟩, ⟨.privateRow 6 24, 60422297292092736000⟩, ⟨.privateRow 6 25, 94335375420119433600⟩, ⟨.privateRow 7 19, 777179921673355200⟩, ⟨.privateRow 7 20, 5016001813312089600⟩, ⟨.privateRow 7 21, 11253465146033510400⟩, ⟨.privateRow 7 22, 21839131248258804480⟩, ⟨.privateRow 7 23, 33369928231076236800⟩, ⟨.privateRow 7 24, 44137812363246201600⟩, ⟨.privateRow 8 17, 561400901552290800⟩, ⟨.privateRow 8 18, 1934150212678934250⟩, ⟨.privateRow 8 19, 4143082336070277600⟩, ⟨.privateRow 8 20, 8256754481867892000⟩, ⟨.privateRow 8 21, 12344395480530553440⟩, ⟨.privateRow 8 22, 16020184309348319100⟩, ⟨.privateRow 8 23, 17194636455476079600⟩, ⟨.privateRow 9 15, 286292558586146112⟩, ⟨.privateRow 9 16, 799345332214549120⟩, ⟨.privateRow 9 17, 1600978123672527600⟩, ⟨.privateRow 9 18, 3159280184013233280⟩, ⟨.privateRow 9 19, 4861483593780253440⟩, ⟨.privateRow 9 20, 6247275072795364608⟩, ⟨.privateRow 9 21, 6776232988567442400⟩, ⟨.privateRow 9 22, 5131306445813708160⟩, ⟨.privateRow 10 12, 2628144662663520⟩, ⟨.privateRow 10 13, 125331781835070720⟩, ⟨.privateRow 10 14, 344211860961416448⟩, ⟨.privateRow 10 15, 665546348383076160⟩, ⟨.privateRow 10 16, 1283754805401748680⟩, ⟨.privateRow 10 17, 2006507996535556800⟩, ⟨.privateRow 10 18, 2666065035653379360⟩, ⟨.privateRow 10 19, 2153126287348964928⟩, ⟨.privateRow 11 10, 4132163205878400⟩, ⟨.privateRow 11 11, 51263261277228000⟩, ⟨.privateRow 11 12, 150599778072307200⟩, ⟨.privateRow 11 13, 297702364645445760⟩, ⟨.privateRow 11 14, 570490302964982400⟩, ⟨.privateRow 11 15, 900644959397383200⟩, ⟨.privateRow 11 16, 901820816899516800⟩, ⟨.privateRow 12 8, 2949958294826400⟩, ⟨.privateRow 12 9, 22482522388972800⟩, ⟨.privateRow 12 10, 66714441436843200⟩, ⟨.privateRow 12 11, 140937867624153600⟩, ⟨.privateRow 12 12, 279882966218375520⟩, ⟨.privateRow 12 13, 325100532081124800⟩, ⟨.privateRow 13 6, 1501796950093440⟩, ⟨.privateRow 13 7, 10768379230065600⟩, ⟨.privateRow 13 8, 31857645361449600⟩, ⟨.privateRow 13 9, 69891319600502400⟩, ⟨.privateRow 13 10, 109641679433395200⟩, ⟨.privateRow 14 4, 563173856285040⟩, ⟨.privateRow 14 5, 5556648715345728⟩, ⟨.privateRow 14 6, 16895215688551200⟩, ⟨.privateRow 14 7, 29804893317239040⟩, ⟨.privateRow 15 3, 3066168773107440⟩, ⟨.privateRow 15 4, 7709224343812992⟩, ⟨.privateRow 16 0, 365020092036600⟩, ⟨.privateRow 16 1, 1159475586469200⟩, ⟨.privateRow 16 2, 410647603541175⟩, ⟨.hall 7 23, 64854523675573632⟩, ⟨.hall 7 24, 527407984304353152⟩, ⟨.hall 6 26, 117336508152985721600⟩, ⟨.hall 5 27, 305682723850715640000⟩, ⟨.hall 4 28, 665095429533302127360⟩, ⟨.hall 3 29, 1246171585827185297280⟩, ⟨.hall 2 30, 1751453252823828153600⟩, ⟨.assumptionRow 17, 5756051186645760⟩]
  caps := #[0, 0, 15384772028745100800, 0, 530448552182065920, 302840010946287360, 439210595047348800, 0, 120059721162110730, 0, 6034635144345600, 7570500258401280, 20872842903267840, 0, 12112101989389584, 10451739260770080, 0, 58565456973354240, 4288100544000000, 0, 0, 0, 0, 0] }

theorem case_56_33_17_checked :
    (Witness.linear .conditional case_56_33_17).check 56 33 17 = true := by
  change case_56_33_17.check 56 33 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_33_18 : Certificate := {
  objectiveScale := 1105525921500000
  eta := 24371652744617499921600
  rows := #[⟨.count 2, 5831879287896977515200⟩, ⟨.count 3, 1378841079296914833600⟩, ⟨.count 4, 324518797554841169280⟩, ⟨.count 5, 76208686232491612800⟩, ⟨.count 6, 19339390224828273600⟩, ⟨.count 7, 4993474859060688000⟩, ⟨.count 8, 1327213054645077600⟩, ⟨.count 9, 362683963447565760⟩, ⟨.count 10, 107003032694157600⟩, ⟨.count 11, 33357220718421600⟩, ⟨.count 12, 9530634490977600⟩, ⟨.count 13, 5631738562850400⟩, ⟨.path 11, 40558563117072⟩, ⟨.path 12, 542236292390520⟩, ⟨.privateRow 2 31, 649401405420842474400⟩, ⟨.privateRow 3 28, 34359862720679496000⟩, ⟨.privateRow 4 26, 20737187736127742880⟩, ⟨.privateRow 4 27, 68517608601825583200⟩, ⟨.privateRow 5 24, 9060791538998751552⟩, ⟨.privateRow 5 25, 23341303647589767840⟩, ⟨.privateRow 5 26, 52031257132937322240⟩, ⟨.privateRow 6 22, 3487401959317676400⟩, ⟨.privateRow 6 23, 8184668228263406880⟩, ⟨.privateRow 6 24, 17860745977715440800⟩, ⟨.privateRow 6 25, 29845919971100032800⟩, ⟨.privateRow 7 19, 86353324630372800⟩, ⟨.privateRow 7 20, 1171401621072883200⟩, ⟨.privateRow 7 21, 2927878303953002400⟩, ⟨.privateRow 7 22, 6315807073617961920⟩, ⟨.privateRow 7 23, 10555755312969266400⟩, ⟨.privateRow 7 24, 15313322901119443200⟩, ⟨.privateRow 8 17, 56578114265673000⟩, ⟨.privateRow 8 18, 407362422712845600⟩, ⟨.privateRow 8 19, 1034362649376856800⟩, ⟨.privateRow 8 20, 2309755887384595650⟩, ⟨.privateRow 8 21, 3887354474162179020⟩, ⟨.privateRow 8 22, 5631621234963673950⟩, ⟨.privateRow 8 23, 6998530224617731800⟩, ⟨.privateRow 9 15, 25230188761569792⟩, ⟨.privateRow 9 16, 147565455873996160⟩, ⟨.privateRow 9 17, 377029253064604140⟩, ⟨.privateRow 9 18, 862281748845316800⟩, ⟨.privateRow 9 19, 1503882779190792000⟩, ⟨.privateRow 9 20, 2198004986207590560⟩, ⟨.privateRow 9 21, 2750134377422151720⟩, ⟨.privateRow 9 22, 2749915365366929760⟩, ⟨.privateRow 10 13, 9369165063651120⟩, ⟨.privateRow 10 14, 54740498830905888⟩, ⟨.privateRow 10 15, 143484183606844080⟩, ⟨.privateRow 10 16, 336003602006061990⟩, ⟨.privateRow 10 17, 608388671603924640⟩, ⟨.privateRow 10 18, 920695392716659560⟩, ⟨.privateRow 10 19, 1180299768002186832⟩, ⟨.privateRow 10 20, 1112127572698882740⟩, ⟨.privateRow 11 11, 2960272834318800⟩, ⟨.privateRow 11 12, 20439666532303200⟩, ⟨.privateRow 11 13, 56923880550657120⟩, ⟨.privateRow 11 14, 138434872707331200⟩, ⟨.privateRow 11 15, 261605086510868100⟩, ⟨.privateRow 11 16, 414520713120571200⟩, ⟨.privateRow 11 17, 558841749698232000⟩, ⟨.privateRow 11 18, 35003421221408640⟩, ⟨.privateRow 12 9, 733125730075200⟩, ⟨.privateRow 12 10, 7545085638690600⟩, ⟨.privateRow 12 11, 23357274680539800⟩, ⟨.privateRow 12 12, 60479818040662020⟩, ⟨.privateRow 12 13, 121030233373849800⟩, ⟨.privateRow 12 14, 202972731425038575⟩, ⟨.privateRow 12 15, 76698915665486400⟩, ⟨.privateRow 13 7, 30943618477200⟩, ⟨.privateRow 13 8, 2665911745728000⟩, ⟨.privateRow 13 9, 9783340708541400⟩, ⟨.privateRow 13 10, 27883013304182400⟩, ⟨.privateRow 13 11, 60476207951839680⟩, ⟨.privateRow 13 12, 51455799347752800⟩, ⟨.privateRow 14 6, 683853968346120⟩, ⟨.privateRow 14 7, 4115501257467600⟩, ⟨.privateRow 14 8, 13375379086769700⟩, ⟨.privateRow 14 9, 24779649676541760⟩, ⟨.privateRow 15 4, 175209644177568⟩, ⟨.privateRow 15 5, 1439222077172880⟩, ⟨.privateRow 15 6, 6604055819000640⟩, ⟨.privateRow 15 7, 2701148681070840⟩, ⟨.privateRow 16 3, 547530138054900⟩, ⟨.privateRow 16 4, 1759918300890750⟩, ⟨.privateRow 17 2, 250299491682240⟩, ⟨.hall 8 24, 3048122179757150496⟩, ⟨.hall 7 25, 16237890715779532800⟩, ⟨.hall 6 26, 46387587627650068800⟩, ⟨.hall 5 27, 107221463696988154800⟩, ⟨.hall 4 28, 217332752777179079040⟩, ⟨.hall 3 29, 395583078334787703360⟩, ⟨.hall 2 30, 598057208281307174400⟩, ⟨.assumptionRow 18, 1186270854743520⟩]
  caps := #[0, 200375784377766204480, 4566661354994225760, 985739128805176200, 100014294561978888, 30563451065373408, 76209631419383280, 6909151290411552, 0, 1054738608295736, 11690059911353226, 1204575408781992, 990795647330280, 0, 3162089234011500, 1186270854743520, 1186270854743520, 37359054502791840, 14291092046256480, 1105525921500000, 0, 0, 0, 0] }

theorem case_56_33_18_checked :
    (Witness.linear .conditional case_56_33_18).check 56 33 18 = true := by
  change case_56_33_18.check 56 33 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_33_19 : Certificate := {
  objectiveScale := 260154130151916000000
  eta := 7317293964764565498952435200
  rows := #[⟨.count 2, 1541665743190568775270691200⟩, ⟨.count 3, 328109618813153121267523200⟩, ⟨.count 4, 68832389700137014872560640⟩, ⟨.count 5, 14328816394765364447155200⟩, ⟨.count 6, 3187936351980029983132800⟩, ⟨.count 7, 723597276317229836121600⟩, ⟨.count 8, 173941652960872556760000⟩, ⟨.count 9, 54269795723792237709120⟩, ⟨.count 10, 18885093750037591876800⟩, ⟨.count 11, 6728292510134850547200⟩, ⟨.count 12, 3364146255067425273600⟩, ⟨.count 13, 993952302633557467200⟩, ⟨.path 10, 563709459454045027200⟩, ⟨.path 11, 10696205022510047040⟩, ⟨.privateRow 2 31, 146076200156540773167048000⟩, ⟨.privateRow 3 28, 6920337687513775334409600⟩, ⟨.privateRow 4 26, 4518730807040244796321320⟩, ⟨.privateRow 4 27, 15645670668781143616866240⟩, ⟨.privateRow 5 24, 1907354710661691437258112⟩, ⟨.privateRow 5 25, 5148573532411564324349280⟩, ⟨.privateRow 5 26, 12238070857919097433482240⟩, ⟨.privateRow 6 22, 678390853071525815020800⟩, ⟨.privateRow 6 23, 1732525126977132902494080⟩, ⟨.privateRow 6 24, 4089589139399587933309200⟩, ⟨.privateRow 6 25, 7416614390913886009051200⟩, ⟨.privateRow 7 19, 8365765213832442015600⟩, ⟨.privateRow 7 20, 210528563910193505433600⟩, ⟨.privateRow 7 21, 586542297698535967588800⟩, ⟨.privateRow 7 22, 1401340219739631554423040⟩, ⟨.privateRow 7 23, 2583447693261721450164000⟩, ⟨.privateRow 7 24, 4123576786192418745590400⟩, ⟨.privateRow 8 17, 3092296052637734342400⟩, ⟨.privateRow 8 18, 65409309082161451031625⟩, ⟨.privateRow 8 19, 194938895354006458254600⟩, ⟨.privateRow 8 20, 492254877879269335630800⟩, ⟨.privateRow 8 21, 931863415462381244082240⟩, ⟨.privateRow 8 22, 1508364033925699854703800⟩, ⟨.privateRow 8 23, 2108656005144000033922200⟩, ⟨.privateRow 9 16, 19928130116998732428800⟩, ⟨.privateRow 9 17, 65498695764933010539960⟩, ⟨.privateRow 9 18, 175244834868769887661440⟩, ⟨.privateRow 9 19, 349635607018239829647360⟩, ⟨.privateRow 9 20, 579836432830101566543424⟩, ⟨.privateRow 9 21, 826222851564144644610000⟩, ⟨.privateRow 9 22, 972527108554567450684800⟩, ⟨.privateRow 10 14, 4880305805930767163952⟩, ⟨.privateRow 10 15, 22098872861886094354080⟩, ⟨.privateRow 10 16, 63998103885818181419340⟩, ⟨.privateRow 10 17, 135759685221134899198560⟩, ⟨.privateRow 10 18, 235682656826127034764240⟩, ⟨.privateRow 10 19, 346670684112532173410016⟩, ⟨.privateRow 10 20, 428194651974536556869760⟩, ⟨.privateRow 10 21, 394930381579733500300800⟩, ⟨.privateRow 11 12, 1056508741260844300800⟩, ⟨.privateRow 11 13, 6797104592624866064160⟩, ⟨.privateRow 11 14, 23880341219683162737600⟩, ⟨.privateRow 11 15, 54934979187862387706400⟩, ⟨.privateRow 11 16, 101252064235308546384000⟩, ⟨.privateRow 11 17, 156789604251324244569600⟩, ⟨.privateRow 11 18, 205289379428546292264000⟩, ⟨.privateRow 11 19, 57553661215954644879600⟩, ⟨.privateRow 12 10, 128491697242158604200⟩, ⟨.privateRow 12 11, 2000647583506006696800⟩, ⟨.privateRow 12 12, 8529512484202201162440⟩, ⟨.privateRow 12 13, 23097356001226813336800⟩, ⟨.privateRow 12 14, 46160642234245478558850⟩, ⟨.privateRow 12 15, 76534327302783924974400⟩, ⟨.privateRow 12 16, 63965503099823683327200⟩, ⟨.privateRow 13 9, 458747216600103446400⟩, ⟨.privateRow 13 10, 2995758338706736142400⟩, ⟨.privateRow 13 11, 9549587892225486742560⟩, ⟨.privateRow 13 12, 21832969382634552912000⟩, ⟨.privateRow 13 13, 41105662054105102561800⟩, ⟨.privateRow 14 7, 68812082490015516960⟩, ⟨.privateRow 14 8, 911122944080761011600⟩, ⟨.privateRow 14 9, 3957737350486347005760⟩, ⟨.privateRow 14 10, 10734684868442420645760⟩, ⟨.privateRow 14 11, 9564029934229564073280⟩, ⟨.privateRow 15 6, 237868927125979564800⟩, ⟨.privateRow 15 7, 1481725191888914372400⟩, ⟨.privateRow 15 8, 5270959180632501720000⟩, ⟨.privateRow 15 9, 556613289474792181632⟩, ⟨.privateRow 16 4, 41414679276398227800⟩, ⟨.privateRow 16 5, 512904874115393436600⟩, ⟨.privateRow 16 6, 1497830900496402572100⟩, ⟨.privateRow 17 3, 141993186090508209600⟩, ⟨.privateRow 17 4, 305831477733402297600⟩, ⟨.hall 8 23, 33048914062565785784400⟩, ⟨.hall 9 23, 46326460238579057617080⟩, ⟨.hall 8 24, 1020179390725714936901184⟩, ⟨.hall 7 25, 5863350119191833282537600⟩, ⟨.hall 6 26, 14150665783288401640873600⟩, ⟨.hall 5 27, 29595426787065490364613600⟩, ⟨.hall 4 28, 56074662298818516426353280⟩, ⟨.hall 3 29, 97555358287694189611048320⟩, ⟨.hall 2 30, 143828874000286299733708800⟩, ⟨.assumptionRow 19, 211154099737802621400⟩]
  caps := #[0, 31662716078484734962118400, 4696798571409469549424400, 222428503103782263888600, 0, 9205533134295968774304, 0, 4594049989472628701280, 444305252432999751255, 601395591906310808992, 0, 233168266196190408240, 118865977749990907590, 403400711886751101600, 1405567288917401566320, 387961136029553902200, 211154099737802621400, 211154099737802621400, 20457714317343203300400, 3170849592237105378600, 260154130151916000000, 0, 0, 0] }

theorem case_56_33_19_checked :
    (Witness.linear .conditional case_56_33_19).check 56 33 19 = true := by
  change case_56_33_19.check 56 33 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_33_20 : Certificate := {
  objectiveScale := 8208569112744000000
  eta := 233174613226458097030636800
  rows := #[⟨.count 2, 48702135595007776840358400⟩, ⟨.count 3, 10198417397207435283888000⟩, ⟨.count 4, 2132282606729014690030080⟩, ⟨.count 5, 445872042486886256841600⟩, ⟨.count 6, 98789965100491785120000⟩, ⟨.count 7, 21604655112826504118400⟩, ⟨.count 8, 4610198371356283305600⟩, ⟨.count 9, 949158488220411268800⟩, ⟨.count 10, 232446976707039494400⟩, ⟨.count 11, 65561967789164985600⟩, ⟨.count 12, 32780983894582492800⟩, ⟨.count 13, 19370581392253291200⟩, ⟨.path 6, 329103222074104077600⟩, ⟨.path 11, 8939399576510541600⟩, ⟨.privateRow 2 31, 5606001219569240499609600⟩, ⟨.privateRow 3 28, 293369607472497456700800⟩, ⟨.privateRow 4 26, 160640715750491350253880⟩, ⟨.privateRow 4 27, 540370132436901121074720⟩, ⟨.privateRow 5 24, 62909449775993168764416⟩, ⟨.privateRow 5 25, 173837408588498711216160⟩, ⟨.privateRow 5 26, 427299529047993801239040⟩, ⟨.privateRow 6 22, 21465473898378461952000⟩, ⟨.privateRow 6 23, 56793253269993832912320⟩, ⟨.privateRow 6 24, 139989039434993174025600⟩, ⟨.privateRow 6 25, 266562157683499809331200⟩, ⟨.privateRow 7 19, 321228808088200412400⟩, ⟨.privateRow 7 20, 6429188204952639984000⟩, ⟨.privateRow 7 21, 18589301276099075121600⟩, ⟨.privateRow 7 22, 46716676829743670830080⟩, ⟨.privateRow 7 23, 91225753066816874906400⟩, ⟨.privateRow 7 24, 154783859045031965548800⟩, ⟨.privateRow 8 17, 164470584599039518800⟩, ⟨.privateRow 8 18, 1924447083631414216875⟩, ⟨.privateRow 8 19, 5931433443819559876200⟩, ⟨.privateRow 8 20, 15866389411224136785000⟩, ⟨.privateRow 8 21, 32100766061730552065880⟩, ⟨.privateRow 8 22, 55768710935855235918600⟩, ⟨.privateRow 8 23, 84224633072780661060600⟩, ⟨.privateRow 9 15, 48211224798497080320⟩, ⟨.privateRow 9 16, 570499493448882117120⟩, ⟨.privateRow 9 17, 1894927124697178211640⟩, ⟨.privateRow 9 18, 5413001355724114152000⟩, ⟨.privateRow 9 19, 11652050393486763099840⟩, ⟨.privateRow 9 20, 20938134929987281982976⟩, ⟨.privateRow 9 21, 32527510731235998878400⟩, ⟨.privateRow 9 22, 42671955949253092862400⟩, ⟨.privateRow 10 13, 5635078223200957440⟩, ⟨.privateRow 10 14, 159226179044322053664⟩, ⟨.privateRow 10 15, 603501224709758094720⟩, ⟨.privateRow 10 16, 1873135220630893259040⟩, ⟨.privateRow 10 17, 4335412838177604474720⟩, ⟨.privateRow 10 18, 8230560033568423430880⟩, ⟨.privateRow 10 19, 13294030009503433750560⟩, ⟨.privateRow 10 20, 18275659279056173914920⟩, ⟨.privateRow 10 21, 19829018485203285758400⟩, ⟨.privateRow 11 12, 33458276950255684800⟩, ⟨.privateRow 11 13, 185957581365631595520⟩, ⟨.privateRow 11 14, 655288556842209628800⟩, ⟨.privateRow 11 15, 1661027354385719720400⟩, ⟨.privateRow 11 16, 3381550065904788835200⟩, ⟨.privateRow 11 17, 5780876841652206571200⟩, ⟨.privateRow 11 18, 8413984538905837288320⟩, ⟨.privateRow 11 19, 10083877659390319092000⟩, ⟨.privateRow 11 20, 260261144860018579200⟩, ⟨.privateRow 12 10, 3300862961607264900⟩, ⟨.privateRow 12 11, 48302283087093142800⟩, ⟨.privateRow 12 12, 226598551171301481480⟩, ⟨.privateRow 12 13, 653494984491075064800⟩, ⟨.privateRow 12 14, 1455509831777686203750⟩, ⟨.privateRow 12 15, 2676723434915968072800⟩, ⟨.privateRow 12 16, 4182307195217149706400⟩, ⟨.privateRow 12 17, 2641600952171772544800⟩, ⟨.privateRow 13 9, 7077712431784856400⟩, ⟨.privateRow 13 10, 69761184734338776000⟩, ⟨.privateRow 13 11, 258820768294953590880⟩, ⟨.privateRow 13 12, 653798512119728606400⟩, ⟨.privateRow 13 13, 1320738390889116229800⟩, ⟨.privateRow 13 14, 2126080955448635961600⟩, ⟨.privateRow 14 8, 14527936044189968400⟩, ⟨.privateRow 14 9, 94563656433091067040⟩, ⟨.privateRow 14 10, 300244011579926013600⟩, ⟨.privateRow 14 11, 690453612292761757440⟩, ⟨.privateRow 14 12, 526153417067080022220⟩, ⟨.privateRow 15 6, 927138938432636160⟩, ⟨.privateRow 15 7, 25361113045042734960⟩, ⟨.privateRow 15 8, 129841594059588727680⟩, ⟨.privateRow 15 9, 373335672033361765728⟩, ⟨.privateRow 15 10, 21427211021554257920⟩, ⟨.privateRow 16 5, 3042174641732087400⟩, ⟨.privateRow 16 6, 43314772279899720600⟩, ⟨.privateRow 16 7, 129944316839699161800⟩, ⟨.privateRow 17 4, 7946905186565452800⟩, ⟨.privateRow 17 5, 41969593016548797600⟩, ⟨.privateRow 18 3, 11258115680967724800⟩, ⟨.hall 9 23, 19177521264377166731040⟩, ⟨.hall 8 24, 97781403496001797091520⟩, ⟨.hall 7 25, 262565747364122560512000⟩, ⟨.hall 6 26, 578421343809373259395200⟩, ⟨.hall 5 27, 1141659175257754708183200⟩, ⟨.hall 4 28, 2078604454657400349039360⟩, ⟨.hall 3 29, 3520852402855949334613440⟩, ⟨.hall 2 30, 5134125108849450598684800⟩, ⟨.assumptionRow 20, 3747438742760753040⟩]
  caps := #[0, 42269052649737129216000, 95691485834173772743200, 925857289263429322800, 170525174099443411248, 134243408776058699040, 66492422673599551200, 0, 18439906400384760060, 954465939984139968, 0, 8666238733352906400, 0, 22003760305773286560, 11556978168080268000, 6781185858299012160, 3747438742760753040, 52658008001099424000, 92718599841935944800, 583343118025398210480, 94755390610167246960, 8208569112744000000, 0, 0] }

theorem case_56_33_20_checked :
    (Witness.linear .conditional case_56_33_20).check 56 33 20 = true := by
  change case_56_33_20.check 56 33 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_33_21 : Certificate := {
  objectiveScale := 60839982835632000000
  eta := 3081373607843855348363539200
  rows := #[⟨.count 2, 531781771937575923017654400⟩, ⟨.count 3, 93049609528385875792627200⟩, ⟨.count 4, 17308528765420030042544640⟩, ⟨.count 5, 3570269338731773114236800⟩, ⟨.count 6, 813370712660715697488000⟩, ⟨.count 7, 197424965549845543910400⟩, ⟨.count 8, 48181092782998019644800⟩, ⟨.count 9, 11633971184187326694720⟩, ⟨.count 10, 2769993139092220641600⟩, ⟨.count 11, 639229185944358609600⟩, ⟨.path 6, 15562255548994188434400⟩, ⟨.path 12, 17990735849072138880⟩, ⟨.path 13, 9671638886249009280⟩, ⟨.privateRow 2 31, 60352106879425104753609600⟩, ⟨.privateRow 4 28, 24242514090852631363629840⟩, ⟨.privateRow 6 27, 38055760589383556028609600⟩, ⟨.privateRow 7 20, 44775560092512345782400⟩, ⟨.privateRow 7 21, 124761610173860725665600⟩, ⟨.privateRow 7 22, 293820726790254822238080⟩, ⟨.privateRow 7 24, 2253487347701893439136000⟩, ⟨.privateRow 7 25, 497675433990235641940800⟩, ⟨.privateRow 8 17, 48964525185973597200⟩, ⟨.privateRow 8 18, 15074953191631621237950⟩, ⟨.privateRow 8 19, 49230332608411739584800⟩, ⟨.privateRow 8 20, 131788019538047936863800⟩, ⟨.privateRow 8 21, 271841250927488216934960⟩, ⟨.privateRow 8 22, 357869473452984528535500⟩, ⟨.privateRow 8 23, 999488370358686052845000⟩, ⟨.privateRow 9 16, 4291468607410663719040⟩, ⟨.privateRow 9 17, 15854713255218250773360⟩, ⟨.privateRow 9 18, 47358488759873663211840⟩, ⟨.privateRow 9 20, 403859403733910229705600⟩, ⟨.privateRow 9 21, 164070330993160329497760⟩, ⟨.privateRow 9 22, 373253311190997666549120⟩, ⟨.privateRow 10 14, 1125624484703838751632⟩, ⟨.privateRow 10 15, 4834897115506421483520⟩, ⟨.privateRow 10 16, 16084846523592326680200⟩, ⟨.privateRow 10 17, 39402253055165055438240⟩, ⟨.privateRow 10 18, 34138066959660791967840⟩, ⟨.privateRow 10 19, 197082493670830505721984⟩, ⟨.privateRow 10 20, 212389223939896017694680⟩, ⟨.privateRow 10 21, 225754440836015982290400⟩, ⟨.privateRow 10 23, 494066048990812445347200⟩, ⟨.privateRow 11 12, 272949101436296376000⟩, ⟨.privateRow 11 13, 1402430092799138282880⟩, ⟨.privateRow 11 14, 5341975890619185417600⟩, ⟨.privateRow 11 15, 14571519852322538305200⟩, ⟨.privateRow 11 16, 31812029097906262233600⟩, ⟨.privateRow 11 17, 37866258191623142080800⟩, ⟨.privateRow 11 18, 106452967099267187118720⟩, ⟨.privateRow 11 19, 149352025179620938474800⟩, ⟨.privateRow 11 21, 259217120191133542838400⟩, ⟨.privateRow 12 10, 59187887587440612000⟩, ⟨.privateRow 12 11, 382568982497002501200⟩, ⟨.privateRow 12 12, 1725918802049768245920⟩, ⟨.privateRow 12 13, 5399908277560831834800⟩, ⟨.privateRow 12 14, 13059807396168771037800⟩, ⟨.privateRow 12 15, 26058735822247603160400⟩, ⟨.privateRow 12 16, 34136614166056372971000⟩, ⟨.privateRow 12 17, 64228328094387054517920⟩, ⟨.privateRow 12 18, 94139814905013979401300⟩, ⟨.privateRow 13 8, 10430313057367156800⟩, ⟨.privateRow 13 9, 92010261613203133200⟩, ⟨.privateRow 13 10, 531810507314590358400⟩, ⟨.privateRow 13 11, 1983547534566737018880⟩, ⟨.privateRow 13 12, 5488331394471765840000⟩, ⟨.privateRow 13 13, 12121141306202496968400⟩, ⟨.privateRow 13 14, 22516917255537861499200⟩, ⟨.privateRow 13 15, 30469924530014427057600⟩, ⟨.privateRow 13 18, 98570431844712914486400⟩, ⟨.privateRow 14 6, 1798696843566377040⟩, ⟨.privateRow 14 7, 17433523253027962080⟩, ⟨.privateRow 14 8, 146893575557920791600⟩, ⟨.privateRow 14 9, 705089162678019799680⟩, ⟨.privateRow 14 10, 2329312412418458266800⟩, ⟨.privateRow 14 11, 5884136940920141423520⟩, ⟨.privateRow 14 12, 12147049458814635745380⟩, ⟨.privateRow 14 14, 65564898210452531610720⟩, ⟨.privateRow 15 6, 30132015499060675200⟩, ⟨.privateRow 15 7, 228501117534543453600⟩, ⟨.privateRow 15 8, 972168390965148511680⟩, ⟨.privateRow 15 9, 2933954349143537944224⟩, ⟨.privateRow 15 10, 6942081570811367780800⟩, ⟨.privateRow 15 12, 34140864932528561887680⟩, ⟨.privateRow 15 13, 29124099580617095614560⟩, ⟨.privateRow 15 17, 50727248092668646699200⟩, ⟨.privateRow 16 5, 56497529060738766000⟩, ⟨.privateRow 16 6, 379475070191295378300⟩, ⟨.privateRow 16 7, 1462258774872029698200⟩, ⟨.privateRow 16 8, 4135054151955470283540⟩, ⟨.privateRow 16 9, 9384867327311606130000⟩, ⟨.privateRow 16 10, 4342541327431033401675⟩, ⟨.privateRow 16 11, 29557085881904490709800⟩, ⟨.privateRow 16 12, 29293027192508704524900⟩, ⟨.privateRow 16 15, 93228455954093729068800⟩, ⟨.privateRow 17 4, 116223488353519747200⟩, ⟨.privateRow 17 5, 699493216942479960000⟩, ⟨.privateRow 17 6, 2502913910805091929600⟩, ⟨.privateRow 17 7, 6799074068680905211200⟩, ⟨.privateRow 17 8, 15015787723698569808000⟩, ⟨.privateRow 17 9, 12884665056080480863200⟩, ⟨.privateRow 17 10, 33527709164077268025600⟩, ⟨.privateRow 17 11, 58113896463581235076800⟩, ⟨.privateRow 17 13, 70089220337636491992000⟩, ⟨.privateRow 17 16, 300670164370555586006400⟩, ⟨.privateRow 18 3, 256122131742015739200⟩, ⟨.privateRow 18 4, 1466604111522732982800⟩, ⟨.privateRow 18 5, 5059243667267609601600⟩, ⟨.privateRow 18 6, 13413481928088995712960⟩, ⟨.privateRow 18 7, 29279231631841227836800⟩, ⟨.privateRow 18 8, 34544472518704372824600⟩, ⟨.privateRow 18 9, 55991434188172910169600⟩, ⟨.privateRow 18 10, 107894497069321058896800⟩, ⟨.privateRow 18 15, 1121595403774250067062400⟩, ⟨.privateRow 19 2, 658599767336611900800⟩, ⟨.privateRow 19 3, 3710112022662913707840⟩, ⟨.privateRow 19 4, 12609191909190042391680⟩, ⟨.privateRow 19 5, 32877300385443666087936⟩, ⟨.privateRow 19 6, 71348308128132955920000⟩, ⟨.privateRow 19 8, 344428861180838406635520⟩, ⟨.privateRow 19 14, 2184970588115943642094080⟩, ⟨.privateRow 20 1, 2502679115879125223040⟩, ⟨.privateRow 20 2, 12200560689910735462320⟩, ⟨.privateRow 20 3, 40668535633035784874400⟩, ⟨.privateRow 20 4, 104111451220571609278464⟩, ⟨.privateRow 20 5, 226840054308710711188320⟩, ⟨.privateRow 20 6, 160640715750491350253880⟩, ⟨.privateRow 20 7, 603056285529873495708960⟩, ⟨.privateRow 20 10, 1577939182561788453126720⟩, ⟨.privateRow 21 0, 12513395579395626115200⟩, ⟨.privateRow 21 1, 54224714177381046499200⟩, ⟨.privateRow 21 2, 177462700944156152179200⟩, ⟨.privateRow 21 3, 455487599090000790593280⟩, ⟨.privateRow 21 4, 957969950467065154819200⟩, ⟨.privateRow 21 10, 9001302553445253718867200⟩, ⟨.privateRow 22 2, 6775378036463761760075040⟩, ⟨.privateRow 22 9, 164544895171262785601822400⟩, ⟨.hall 20 5, 33663983393727627158400⟩, ⟨.hall 21 10, 940305839030494056338400⟩, ⟨.hall 18 14, 17694380415776973068160⟩, ⟨.hall 13 15, 3261414194165247120⟩, ⟨.hall 8 18, 14235087132523713456⟩, ⟨.hall 12 18, 45445617146085979680⟩, ⟨.hall 9 19, 44887558001375253528⟩, ⟨.hall 11 20, 677509144410002018400⟩, ⟨.hall 6 23, 1630684893064125923024⟩, ⟨.hall 8 23, 2742013410414521443200⟩, ⟨.hall 7 25, 3229760345297816592662400⟩, ⟨.hall 3 27, 52261405560613801712160⟩, ⟨.hall 4 28, 37774057786601789702649600⟩, ⟨.hall 2 30, 61894887456988010657232000⟩]
  caps := #[0, 0, 0, 0, 3423559426217117307120, 0, 3774795567489197565600, 691911359573198173552, 0, 2923988120133992704, 0, 355034720072476679040, 99741059033279335200, 29637936355334959680, 0, 130157130256456105712, 2093467514851057424625, 0, 0, 85628746239008379084288, 104807105057761756969176, 0, 60839982835632000000, 0] }

theorem case_56_33_21_checked :
    (Witness.linear .conditional case_56_33_21).check 56 33 21 = true := by
  change case_56_33_21.check 56 33 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_34_1_checked :
    (Witness.rising).check 56 34 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_34_2_checked :
    (Witness.rising).check 56 34 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_34_3_checked :
    (Witness.rising).check 56 34 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_34_4_checked :
    (Witness.rising).check 56 34 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_34_5_checked :
    (Witness.rising).check 56 34 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_34_6_checked :
    (Witness.rising).check 56 34 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_34_7_checked :
    (Witness.rising).check 56 34 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_34_8_checked :
    (Witness.rising).check 56 34 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_34_9_checked :
    (Witness.rising).check 56 34 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_34_10_checked :
    (Witness.rising).check 56 34 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_34_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_34_11_checked :
    (Witness.linear .positive case_56_34_11).check 56 34 11 = true := by
  change case_56_34_11.check 56 34 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_34_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_34_12_checked :
    (Witness.linear .positive case_56_34_12).check 56 34 12 = true := by
  change case_56_34_12.check 56 34 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_34_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_34_13_checked :
    (Witness.linear .positive case_56_34_13).check 56 34 13 = true := by
  change case_56_34_13.check 56 34 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_34_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_34_14_checked :
    (Witness.linear .positive case_56_34_14).check 56 34 14 = true := by
  change case_56_34_14.check 56 34 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_34_15 : Certificate := {
  objectiveScale := 21743429760000000
  eta := 1675200958767961488864000
  rows := #[⟨.count 2, 325222164156417431904000⟩, ⟨.count 3, 67832432515807327368000⟩, ⟨.count 4, 13598080556499056217600⟩, ⟨.count 5, 2848145400877624848000⟩, ⟨.count 6, 597189557204656416000⟩, ⟨.count 7, 126840831781798134000⟩, ⟨.count 8, 28331399463512745600⟩, ⟨.count 9, 6194912419135440000⟩, ⟨.count 10, 1524901518556416000⟩, ⟨.count 11, 349456598002512000⟩, ⟨.count 12, 95306344909776000⟩, ⟨.path 12, 8301394856891136⟩, ⟨.path 13, 14627472914454400⟩, ⟨.privateRow 2 32, 10538372013271934832000⟩, ⟨.privateRow 3 31, 27813298288192384968000⟩, ⟨.privateRow 6 22, 44033044147442064000⟩, ⟨.privateRow 6 23, 113802835551525120000⟩, ⟨.privateRow 7 19, 3401465800506774000⟩, ⟨.privateRow 7 20, 24469904055584988000⟩, ⟨.privateRow 7 21, 51358773912927624000⟩, ⟨.privateRow 7 22, 91022192336158083000⟩, ⟨.privateRow 7 23, 102494825974595854800⟩, ⟨.privateRow 7 24, 160616010533626147500⟩, ⟨.privateRow 8 17, 3579971054658158160⟩, ⟨.privateRow 8 18, 10209368627535677600⟩, ⟨.privateRow 8 19, 20956442268982270050⟩, ⟨.privateRow 8 21, 133333444158853138200⟩, ⟨.privateRow 8 22, 35818983607441114080⟩, ⟨.privateRow 8 24, 126158244209689692000⟩, ⟨.privateRow 9 14, 292537530903618000⟩, ⟨.privateRow 9 15, 1887258167284089600⟩, ⟨.privateRow 9 16, 4487869885862563200⟩, ⟨.privateRow 9 17, 8444965794085620800⟩, ⟨.privateRow 9 19, 35873459503952241600⟩, ⟨.privateRow 9 20, 54228427787505972000⟩, ⟨.privateRow 9 21, 38915063169804581760⟩, ⟨.privateRow 10 12, 296915920680456000⟩, ⟨.privateRow 10 13, 903821837561042400⟩, ⟨.privateRow 10 14, 2036090095799760000⟩, ⟨.privateRow 10 15, 3668341215577278240⟩, ⟨.privateRow 10 16, 5917465059509203200⟩, ⟨.privateRow 10 17, 1887065629213564800⟩, ⟨.privateRow 10 18, 21781584369522806400⟩, ⟨.privateRow 10 19, 30806187553003262400⟩, ⟨.privateRow 10 20, 26657184671264347200⟩, ⟨.privateRow 10 21, 12039574020727453200⟩, ⟨.privateRow 11 9, 25944505003216800⟩, ⟨.privateRow 11 10, 174160999329174000⟩, ⟨.privateRow 11 11, 472866095898504000⟩, ⟨.privateRow 11 12, 976228185707775000⟩, ⟨.privateRow 11 13, 1756669220950644000⟩, ⟨.privateRow 11 14, 2802800759888329200⟩, ⟨.privateRow 11 15, 4901217033600888000⟩, ⟨.privateRow 11 16, 1821741071973322500⟩, ⟨.privateRow 11 17, 13474501811291664000⟩, ⟨.privateRow 11 18, 19529858511094932000⟩, ⟨.privateRow 11 19, 18784880581716849600⟩, ⟨.privateRow 12 6, 934375930488000⟩, ⟨.privateRow 12 7, 28294071145089750⟩, ⟨.privateRow 12 8, 101660101237094400⟩, ⟨.privateRow 12 9, 262092448501884000⟩, ⟨.privateRow 12 10, 530294278087728000⟩, ⟨.privateRow 12 11, 937840907896893000⟩, ⟨.privateRow 12 12, 1523457483027480000⟩, ⟨.privateRow 12 13, 2654281705737261600⟩, ⟨.privateRow 12 14, 4142296138948968000⟩, ⟨.privateRow 12 15, 1940874003110542500⟩, ⟨.privateRow 12 16, 9152812909370988000⟩, ⟨.privateRow 12 17, 14736743581674114000⟩, ⟨.privateRow 12 19, 34286457581291916000⟩, ⟨.privateRow 13 4, 3706357857602400⟩, ⟨.privateRow 13 5, 21303771215126400⟩, ⟨.privateRow 13 6, 66118776781157100⟩, ⟨.privateRow 13 7, 160750035081155520⟩, ⟨.privateRow 13 8, 328806889938727200⟩, ⟨.privateRow 13 9, 586500584060160000⟩, ⟨.privateRow 13 11, 3605179101541617600⟩, ⟨.privateRow 13 12, 1721232589070554560⟩, ⟨.privateRow 13 13, 4016632958253115200⟩, ⟨.privateRow 13 15, 11834324999368185600⟩, ⟨.privateRow 13 16, 10142183537481996000⟩, ⟨.privateRow 14 3, 26003336080321600⟩, ⟨.privateRow 14 4, 43728793546838400⟩, ⟨.privateRow 14 5, 115294203356131800⟩, ⟨.privateRow 14 6, 235865554328564160⟩, ⟨.privateRow 14 7, 432660549907872000⟩, ⟨.privateRow 14 8, 719033424374865600⟩, ⟨.privateRow 14 9, 1147206003543600⟩, ⟨.privateRow 14 10, 4405271053607424000⟩, ⟨.privateRow 14 11, 2303130772714131360⟩, ⟨.privateRow 14 13, 9996179511877158600⟩, ⟨.privateRow 14 14, 4662900744688929600⟩, ⟨.privateRow 14 15, 12986371960113552000⟩, ⟨.privateRow 15 1, 21555397013950800⟩, ⟨.privateRow 15 2, 45505838140562800⟩, ⟨.privateRow 15 3, 92113893813942000⟩, ⟨.privateRow 15 4, 203270563752881625⟩, ⟨.privateRow 15 5, 379036863570805440⟩, ⟨.privateRow 15 6, 648744995003905800⟩, ⟨.privateRow 15 7, 1167502725144756000⟩, ⟨.privateRow 15 9, 6051303085782754800⟩, ⟨.privateRow 15 11, 8796010831169962400⟩, ⟨.privateRow 15 12, 6028854350122503900⟩, ⟨.privateRow 15 13, 10373036684041231200⟩, ⟨.privateRow 15 14, 13386746855350268400⟩, ⟨.privateRow 15 17, 27544416145081836000⟩, ⟨.privateRow 16 0, 86946139215936000⟩, ⟨.privateRow 16 2, 373516778212578000⟩, ⟨.privateRow 16 3, 316198654726704750⟩, ⟨.privateRow 16 4, 702090074168683200⟩, ⟨.privateRow 16 6, 4201421371439292000⟩, ⟨.privateRow 16 8, 8949771199463094000⟩, ⟨.privateRow 16 10, 16559918661151866000⟩, ⟨.privateRow 16 13, 21467092341309615000⟩, ⟨.privateRow 16 16, 135582541528800366000⟩, ⟨.privateRow 17 0, 627139281937168000⟩, ⟨.privateRow 17 1, 583050580624512000⟩, ⟨.privateRow 17 2, 739947872285622000⟩, ⟨.privateRow 17 3, 1762108421442969600⟩, ⟨.privateRow 17 5, 9107050735823040000⟩, ⟨.privateRow 17 6, 1399591324323192000⟩, ⟨.privateRow 17 7, 16407131679770832000⟩, ⟨.privateRow 17 8, 5960882394412545600⟩, ⟨.privateRow 17 9, 24840833996730752000⟩, ⟨.privateRow 17 11, 24523986624323472000⟩, ⟨.privateRow 17 14, 113504561990603784000⟩, ⟨.privateRow 17 17, 542398998475414080000⟩, ⟨.privateRow 18 0, 6222445363220486400⟩, ⟨.privateRow 18 3, 10197022505783256000⟩, ⟨.privateRow 18 4, 9721247180797152000⟩, ⟨.privateRow 18 6, 58635158921481542400⟩, ⟨.privateRow 18 8, 36768717217574742400⟩, ⟨.privateRow 18 9, 14626876545180900000⟩, ⟨.privateRow 19 0, 17245087446768281100⟩, ⟨.privateRow 19 1, 44793346731961988160⟩, ⟨.privateRow 19 3, 42449446022814230400⟩, ⟨.privateRow 19 4, 19482999558180958800⟩, ⟨.privateRow 19 8, 1004954179913198915400⟩, ⟨.privateRow 20 0, 235668234895954660800⟩, ⟨.privateRow 20 1, 320153073820919539200⟩, ⟨.privateRow 20 3, 147848468118688537200⟩, ⟨.privateRow 20 4, 38806433190414489600⟩, ⟨.privateRow 20 7, 2679614529324050518200⟩, ⟨.privateRow 20 12, 10916330503199409288000⟩, ⟨.hall 17 4, 718609840619711040⟩, ⟨.hall 14 7, 122445594341070⟩, ⟨.hall 13 9, 102804770296800⟩, ⟨.hall 18 9, 293478560723307960⟩, ⟨.hall 17 10, 33814498635918000⟩, ⟨.hall 9 13, 18780223119372⟩, ⟨.hall 10 13, 58292628966000⟩, ⟨.hall 20 13, 72568030066075095552000⟩, ⟨.hall 11 15, 123812828889750⟩, ⟨.hall 7 18, 486779126433600⟩, ⟨.hall 13 20, 3475050871305499200⟩, ⟨.hall 8 25, 19228584565241251200⟩, ⟨.hall 6 27, 1118417688317533032000⟩, ⟨.hall 4 29, 11854650484323382095360⟩, ⟨.hall 3 30, 16351043681515189046400⟩]
  caps := #[0, 1694225305090871329920, 0, 0, 2534308367430285056, 349648085340537984, 826142036853344640, 0, 0, 11878840180658880, 2656421105834496, 229995863707014328, 43461357004198636, 50747240694730960, 56518780408685920, 0, 2016341391766952250, 0, 78696116127200, 0, 299890860657695307000, 0, 0] }

theorem case_56_34_15_checked :
    (Witness.linear .positive case_56_34_15).check 56 34 15 = true := by
  change case_56_34_15.check 56 34 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_34_16 : Certificate := {
  objectiveScale := 1207968320000000
  eta := 93208201719226802208000
  rows := #[⟨.count 2, 20446139487199634208000⟩, ⟨.count 3, 4292961671689602912000⟩, ⟨.count 4, 929056647236304787200⟩, ⟨.count 5, 202755103237198512000⟩, ⟨.count 6, 43552111552709760000⟩, ⟨.count 7, 9921246101554788000⟩, ⟨.count 8, 2190120552219600000⟩, ⟨.count 9, 518119947782236800⟩, ⟨.count 10, 121298984430624000⟩, ⟨.count 11, 31768781636592000⟩, ⟨.count 12, 8664213173616000⟩, ⟨.path 12, 1605003514033920⟩, ⟨.privateRow 2 32, 2207115887704824096000⟩, ⟨.privateRow 5 24, 5035191441007728000⟩, ⟨.privateRow 6 22, 4151395854901152000⟩, ⟨.privateRow 6 23, 10729504876778688000⟩, ⟨.privateRow 7 19, 101684168495910000⟩, ⟨.privateRow 7 20, 2032118998095186000⟩, ⟨.privateRow 7 21, 4620707401805352000⟩, ⟨.privateRow 7 22, 8665837713586053000⟩, ⟨.privateRow 7 25, 94699248306152490000⟩, ⟨.privateRow 7 27, 278081170887145626000⟩, ⟨.privateRow 8 17, 157250655649367280⟩, ⟨.privateRow 8 18, 787956705343007200⟩, ⟨.privateRow 8 19, 1830393251517530700⟩, ⟨.privateRow 8 20, 3309585028768418400⟩, ⟨.privateRow 8 21, 6465965910336332400⟩, ⟨.privateRow 8 22, 4851993071387301840⟩, ⟨.privateRow 8 23, 7560843676400114100⟩, ⟨.privateRow 9 15, 104898241514102400⟩, ⟨.privateRow 9 16, 318255803673968160⟩, ⟨.privateRow 9 17, 712519219655443200⟩, ⟨.privateRow 9 18, 1302808854206059200⟩, ⟨.privateRow 9 19, 2499597995149569600⟩, ⟨.privateRow 9 20, 4089267945358596000⟩, ⟨.privateRow 9 21, 4179500912110043520⟩, ⟨.privateRow 9 22, 5755636811233108800⟩, ⟨.privateRow 9 24, 17206838555695588800⟩, ⟨.privateRow 10 12, 4132163205878400⟩, ⟨.privateRow 10 13, 50324638183419600⟩, ⟨.privateRow 10 14, 140832846858412800⟩, ⟨.privateRow 10 15, 292937047399956960⟩, ⟨.privateRow 10 16, 534004338600532800⟩, ⟨.privateRow 10 17, 1036564803558484200⟩, ⟨.privateRow 10 18, 1697690684133100800⟩, ⟨.privateRow 10 19, 2589155703382248000⟩, ⟨.privateRow 10 20, 2954669976466528320⟩, ⟨.privateRow 10 23, 21734611956674416800⟩, ⟨.privateRow 11 10, 4280533889346000⟩, ⟨.privateRow 11 11, 23215648119048000⟩, ⟨.privateRow 11 12, 65101935096198000⟩, ⟨.privateRow 11 13, 134098390255284000⟩, ⟨.privateRow 11 14, 238338064050886800⟩, ⟨.privateRow 11 15, 464498095141080000⟩, ⟨.privateRow 11 16, 782486752242195000⟩, ⟨.privateRow 11 17, 1203397322578308000⟩, ⟨.privateRow 11 18, 1748606689247418000⟩, ⟨.privateRow 11 19, 830176025585306400⟩, ⟨.privateRow 11 23, 34329778647159996000⟩, ⟨.privateRow 12 8, 2936205575503200⟩, ⟨.privateRow 12 10, 55373208551892000⟩, ⟨.privateRow 12 12, 233933755687632000⟩, ⟨.privateRow 12 13, 177544168282681200⟩, ⟨.privateRow 12 14, 402885912573144000⟩, ⟨.privateRow 12 15, 641242027068142500⟩, ⟨.privateRow 12 16, 946152707637852000⟩, ⟨.privateRow 12 17, 1327549996268496000⟩, ⟨.privateRow 12 18, 1057322814286939200⟩, ⟨.privateRow 13 6, 1786993967058300⟩, ⟨.privateRow 13 7, 3119116742501760⟩, ⟨.privateRow 13 8, 12748770812606400⟩, ⟨.privateRow 13 9, 52251870216268800⟩, ⟨.privateRow 13 10, 3249079940106000⟩, ⟨.privateRow 13 11, 261501706694592000⟩, ⟨.privateRow 13 12, 182901540095033760⟩, ⟨.privateRow 13 13, 386905252719585600⟩, ⟨.privateRow 13 14, 601404696913620600⟩, ⟨.privateRow 13 15, 864069602357332800⟩, ⟨.privateRow 13 16, 1186563994126711200⟩, ⟨.privateRow 13 18, 2429228768552586000⟩, ⟨.privateRow 14 4, 1030644965750400⟩, ⟨.privateRow 14 5, 3050525054877300⟩, ⟨.privateRow 14 6, 6507786783738240⟩, ⟨.privateRow 14 7, 20649708063784800⟩, ⟨.privateRow 14 8, 64692791696332800⟩, ⟨.privateRow 14 9, 5318864198247600⟩, ⟨.privateRow 14 10, 320724666841924800⟩, ⟨.privateRow 14 12, 895794069676105600⟩, ⟨.privateRow 14 13, 431610185969562600⟩, ⟨.privateRow 14 15, 3080560993879168800⟩, ⟨.privateRow 14 20, 11983088164287240000⟩, ⟨.privateRow 15 2, 730040184073200⟩, ⟨.privateRow 15 4, 10539955157556825⟩, ⟨.privateRow 15 5, 9198506319322320⟩, ⟨.privateRow 15 6, 31130999277978600⟩, ⟨.privateRow 15 7, 69073032800772000⟩, ⟨.privateRow 15 9, 566444815551342000⟩, ⟨.privateRow 15 11, 292259420357304400⟩, ⟨.privateRow 15 13, 4175621269988968800⟩, ⟨.privateRow 15 16, 3571539090532112700⟩, ⟨.privateRow 16 2, 6625574779824000⟩, ⟨.privateRow 16 3, 17305863292092375⟩, ⟨.privateRow 16 4, 6883236021261600⟩, ⟨.privateRow 16 5, 82799965775241000⟩, ⟨.privateRow 16 6, 118049904490518000⟩, ⟨.privateRow 16 8, 909611107272504000⟩, ⟨.privateRow 16 9, 232778527264483200⟩, ⟨.privateRow 16 10, 375970694797698000⟩, ⟨.privateRow 16 11, 208843638372369000⟩, ⟨.privateRow 16 13, 905771285525106000⟩, ⟨.privateRow 17 0, 2085829097352000⟩, ⟨.privateRow 17 2, 74307661593165000⟩, ⟨.privateRow 17 4, 193088179297728000⟩, ⟨.privateRow 17 5, 269553298734720000⟩, ⟨.privateRow 17 7, 84191647202208000⟩, ⟨.privateRow 17 8, 3705683974355563200⟩, ⟨.privateRow 17 10, 567866971754082000⟩, ⟨.privateRow 17 12, 905249828250768000⟩, ⟨.privateRow 17 14, 1357874742376152000⟩, ⟨.privateRow 18 1, 255305481515884800⟩, ⟨.privateRow 18 4, 1659485629853251200⟩, ⟨.privateRow 18 7, 7497470973849816960⟩, ⟨.privateRow 18 8, 4448934409378659200⟩, ⟨.privateRow 18 9, 909525777900339600⟩, ⟨.privateRow 18 10, 905726589187305600⟩, ⟨.privateRow 18 12, 3982765511647802880⟩, ⟨.privateRow 19 0, 765916444547654400⟩, ⟨.privateRow 19 2, 875333079483033600⟩, ⟨.privateRow 19 5, 17790150143811427200⟩, ⟨.privateRow 19 6, 7429389512112247680⟩, ⟨.privateRow 19 8, 44710372450469325600⟩, ⟨.privateRow 20 0, 8731447467843260160⟩, ⟨.privateRow 20 2, 1212701037200452800⟩, ⟨.privateRow 20 5, 66334746734864768160⟩, ⟨.privateRow 20 9, 498824359968452918400⟩, ⟨.privateRow 21 3, 425547818508522528000⟩, ⟨.privateRow 21 5, 299132922509445024000⟩, ⟨.privateRow 21 8, 1495664612547225120000⟩, ⟨.privateRow 21 12, 8106906433685026968000⟩, ⟨.hall 18 13, 149536067745018240⟩, ⟨.hall 17 15, 208061452460862000⟩, ⟨.hall 11 16, 35978476248000⟩, ⟨.hall 16 17, 454710743222736000⟩, ⟨.hall 12 18, 761005736712000⟩, ⟨.hall 14 18, 14570065147397760⟩, ⟨.hall 9 23, 14529885492154032⟩, ⟨.hall 6 25, 96505887650744000⟩, ⟨.hall 8 25, 1256792255350632000⟩, ⟨.hall 5 28, 688913963685851904000⟩, ⟨.hall 4 29, 1228325732669224949760⟩, ⟨.hall 3 30, 1841232248964958449600⟩, ⟨.hall 2 31, 2154818155475554569000⟩]
  caps := #[0, 9527957294949350400, 0, 0, 524317490425747200, 0, 0, 26758031043595280, 3757569216333920, 1252408558103040, 1813962689880000, 960686252139060, 1053084618001020, 7441565841228160, 4775450571968960, 1207968320000000, 0, 451067522849299200, 0, 7668614063948235840, 0, 0, 0] }

theorem case_56_34_16_checked :
    (Witness.linear .positive case_56_34_16).check 56 34 16 = true := by
  change case_56_34_16.check 56 34 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_34_17 : Certificate := {
  objectiveScale := 2141759620000000
  eta := 132172286044477350672000
  rows := #[⟨.count 2, 27576821585938296672000⟩, ⟨.count 3, 5577212070084882427200⟩, ⟨.count 4, 1238486890833557164800⟩, ⟨.count 5, 263602909665151056000⟩, ⟨.count 6, 60597506936270304000⟩, ⟨.count 7, 13994870328683244000⟩, ⟨.count 8, 3206336488449494400⟩, ⟨.count 9, 810970353050457600⟩, ⟨.count 10, 207941116166784000⟩, ⟨.count 11, 47653172454888000⟩, ⟨.count 12, 25992639520848000⟩, ⟨.path 12, 2411627375469312⟩, ⟨.privateRow 2 32, 2146480835844801456000⟩, ⟨.privateRow 3 29, 212222681510079240000⟩, ⟨.privateRow 3 30, 733077776987673717600⟩, ⟨.privateRow 4 27, 141742412019100292400⟩, ⟨.privateRow 4 28, 267113360035994472000⟩, ⟨.privateRow 4 29, 486548421398897457600⟩, ⟨.privateRow 5 24, 12233387655969480000⟩, ⟨.privateRow 5 25, 52158909873695264640⟩, ⟨.privateRow 5 26, 97111822531604680800⟩, ⟨.privateRow 5 27, 176841596863336204800⟩, ⟨.privateRow 6 22, 8393972238915120000⟩, ⟨.privateRow 6 23, 19085336240770800000⟩, ⟨.privateRow 6 24, 34556347821650054400⟩, ⟨.privateRow 6 25, 62089917655425660000⟩, ⟨.privateRow 6 26, 85164402044882160000⟩, ⟨.privateRow 7 19, 495905867895438000⟩, ⟨.privateRow 7 20, 3540955621392189000⟩, ⟨.privateRow 7 21, 7476132942183906000⟩, ⟨.privateRow 7 22, 12558776995156392000⟩, ⟨.privateRow 7 23, 22250999061821930400⟩, ⟨.privateRow 7 24, 30288193958329807500⟩, ⟨.privateRow 7 25, 35479952945957520000⟩, ⟨.privateRow 7 26, 18007484054714154000⟩, ⟨.privateRow 8 17, 410647603541175000⟩, ⟨.privateRow 8 18, 1411167675813495600⟩, ⟨.privateRow 8 19, 2947628498218554150⟩, ⟨.privateRow 8 20, 4859251756646086800⟩, ⟨.privateRow 8 21, 8308222314845052600⟩, ⟨.privateRow 8 22, 11323361279085775920⟩, ⟨.privateRow 8 23, 13093088191306823700⟩, ⟨.privateRow 8 24, 12058803760521117600⟩, ⟨.privateRow 8 25, 3360739987380976200⟩, ⟨.privateRow 9 14, 625748729205600⟩, ⟨.privateRow 9 15, 227658764934619200⟩, ⟨.privateRow 9 16, 599967881562329280⟩, ⟨.privateRow 9 17, 1193511409504814400⟩, ⟨.privateRow 9 18, 1976270924013586200⟩, ⟨.privateRow 9 19, 3352225335030000000⟩, ⟨.privateRow 9 20, 4543561522761861600⟩, ⟨.privateRow 9 21, 5303595929254983360⟩, ⟨.privateRow 9 22, 2037750736658036400⟩, ⟨.privateRow 10 12, 7197961713465600⟩, ⟨.privateRow 10 13, 102021110119328400⟩, ⟨.privateRow 10 14, 274104198583488000⟩, ⟨.privateRow 10 15, 521152422393002400⟩, ⟨.privateRow 10 16, 855446647341686400⟩, ⟨.privateRow 10 17, 1467934316939890800⟩, ⟨.privateRow 10 18, 2031139116843408000⟩, ⟨.privateRow 10 19, 835230149936582400⟩, ⟨.privateRow 11 10, 6188723695440000⟩, ⟨.privateRow 11 11, 45986977613808000⟩, ⟨.privateRow 11 12, 128699666516421000⟩, ⟨.privateRow 11 13, 252049837777920000⟩, ⟨.privateRow 11 14, 410250493770717600⟩, ⟨.privateRow 11 15, 707096064002328000⟩, ⟨.privateRow 11 16, 281045414819169000⟩, ⟨.privateRow 12 8, 3754492375233600⟩, ⟨.privateRow 12 9, 22434123395970000⟩, ⟨.privateRow 12 10, 63815262413364000⟩, ⟨.privateRow 12 11, 132309755338761000⟩, ⟨.privateRow 12 12, 224481886770960000⟩, ⟨.privateRow 12 13, 64115177484758400⟩, ⟨.privateRow 13 6, 1949447964063600⟩, ⟨.privateRow 13 7, 11956614179590080⟩, ⟨.privateRow 13 8, 34718739931418400⟩, ⟨.privateRow 13 9, 75978484753248000⟩, ⟨.privateRow 13 10, 5415133233510000⟩, ⟨.privateRow 14 4, 883409970643200⟩, ⟨.privateRow 14 5, 6805017430110900⟩, ⟨.privateRow 14 6, 21275456792990400⟩, ⟨.privateRow 14 7, 536356053604800⟩, ⟨.privateRow 15 2, 365020092036600⟩, ⟨.privateRow 15 3, 4251410483720400⟩, ⟨.privateRow 15 4, 1231942810623525⟩, ⟨.privateRow 16 1, 782185911507000⟩, ⟨.hall 7 26, 2752251493955964000⟩, ⟨.hall 6 27, 43010391938568912000⟩, ⟨.hall 5 28, 210274876758858912000⟩, ⟨.hall 4 29, 530703504427069733760⟩, ⟨.hall 3 30, 543603019772177164800⟩, ⟨.hall 2 31, 1016395056803629503000⟩, ⟨.assumptionRow 17, 2929725640050300⟩]
  caps := #[0, 0, 0, 0, 2389923952966286100, 496695140337474000, 258696420324689880, 26081900005417256, 0, 8126000481965912, 6144168366953712, 21610258299388776, 0, 6647417300150900, 16379365674363900, 1469645271903900, 25795458977733900, 31338428279949700, 2141759620000000, 0, 0, 0, 0] }

theorem case_56_34_17_checked :
    (Witness.linear .conditional case_56_34_17).check 56 34 17 = true := by
  change case_56_34_17.check 56 34 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_34_18 : Certificate := {
  objectiveScale := 72301473981178387545600000
  eta := 5632859010531274781602366479456000
  rows := #[⟨.count 2, 956933577078672163669900096896000⟩, ⟨.count 3, 176525246983830812010318692116800⟩, ⟨.count 4, 38231556787592883093988831622400⟩, ⟨.count 5, 8266970030583956756850545760000⟩, ⟨.count 6, 1758133897906995328379980320000⟩, ⟨.count 7, 409140202305484285194809250000⟩, ⟨.count 8, 97757232337523711875879756800⟩, ⟨.count 9, 24688688779119508866612489600⟩, ⟨.count 10, 6905926931222240242409088000⟩, ⟨.count 11, 2373912382607645083328124000⟩, ⟨.count 12, 863240866402780030301136000⟩, ⟨.path 3, 3381300896691376136240614051200⟩, ⟨.path 10, 23448033514970987674752000⟩, ⟨.path 11, 112415348893519627802919072⟩, ⟨.privateRow 2 32, 91826959416640258129939908288000⟩, ⟨.privateRow 3 29, 8900771066262060108209087601600⟩, ⟨.privateRow 3 30, 27970975138095025996159327327200⟩, ⟨.privateRow 4 27, 5026953699366629089454120325600⟩, ⟨.privateRow 4 28, 10041188983301590553128470580800⟩, ⟨.privateRow 4 29, 19201627697960198021007863786400⟩, ⟨.privateRow 5 24, 314427492616227415110982296000⟩, ⟨.privateRow 5 25, 1772947111174467033699947813760⟩, ⟨.privateRow 5 26, 3559036584961657280705658033600⟩, ⟨.privateRow 5 27, 6966865342013488343807383008000⟩, ⟨.privateRow 6 22, 206807847565351730116429296000⟩, ⟨.privateRow 6 23, 621373564390297403292688080000⟩, ⟨.privateRow 6 24, 1244908428134995841031611596800⟩, ⟨.privateRow 6 25, 2433020403043279882625132340000⟩, ⟨.privateRow 6 26, 3657167888341288863928001616000⟩, ⟨.privateRow 7 20, 94686732533554934573655855000⟩, ⟨.privateRow 7 21, 230387682898222906063166874000⟩, ⟨.privateRow 7 22, 443897636634673997803739712000⟩, ⟨.privateRow 7 23, 869060548577112105672082825200⟩, ⟨.privateRow 7 24, 1313340049400604555475337692500⟩, ⟨.privateRow 7 25, 1721817834235689485160783918000⟩, ⟨.privateRow 7 26, 1132967668784215340602311786000⟩, ⟨.privateRow 8 17, 2465751619227718625440717080⟩, ⟨.privateRow 8 18, 35010278644688551574595825600⟩, ⟨.privateRow 8 19, 89165288089108541886788762550⟩, ⟨.privateRow 8 20, 166368095977475781339786435600⟩, ⟨.privateRow 8 21, 322293375362773487590791073200⟩, ⟨.privateRow 8 22, 494023156277128758229892342400⟩, ⟨.privateRow 8 23, 648241736532809301462655775700⟩, ⟨.privateRow 8 24, 710412863274251557955147012400⟩, ⟨.privateRow 8 25, 407394537442314218911311397200⟩, ⟨.privateRow 9 15, 1711658404796623433819323200⟩, ⟨.privateRow 9 16, 12967796126406206677412620800⟩, ⟨.privateRow 9 17, 34414535873924163874671955200⟩, ⟨.privateRow 9 18, 66257333333356712242405109400⟩, ⟨.privateRow 9 19, 127095089782841050334256936000⟩, ⟨.privateRow 9 20, 197280911262779038443394245600⟩, ⟨.privateRow 9 21, 263296137504993711731004712320⟩, ⟨.privateRow 9 22, 294051011683629200932772240400⟩, ⟨.privateRow 9 23, 134873392404449168808346008000⟩, ⟨.privateRow 10 13, 784110453649191860856865200⟩, ⟨.privateRow 10 14, 5030339957856199994754801600⟩, ⟨.privateRow 10 15, 13691000141148091280576016960⟩, ⟨.privateRow 10 16, 27451059551608404963576124800⟩, ⟨.privateRow 10 17, 54243897942584690154047633400⟩, ⟨.privateRow 10 18, 85534837848138318430981132800⟩, ⟨.privateRow 10 19, 117213722309724148447722583200⟩, ⟨.privateRow 10 20, 85495375408531334201024509440⟩, ⟨.privateRow 11 11, 287746955467593343433712000⟩, ⟨.privateRow 11 12, 2026218144750969793345722000⟩, ⟨.privateRow 11 13, 5761478812885221262843188000⟩, ⟨.privateRow 11 14, 12027822738545401755529161600⟩, ⟨.privateRow 11 15, 24770217083168660313918708000⟩, ⟨.privateRow 11 16, 41084869985357312067144691500⟩, ⟨.privateRow 11 17, 44035560863522767021909140000⟩, ⟨.privateRow 12 9, 82213415847883812409632000⟩, ⟨.privateRow 12 10, 830039294618057721443400000⟩, ⟨.privateRow 12 11, 2583727870969431896248539000⟩, ⟨.privateRow 12 12, 5689542074018322926984760000⟩, ⟨.privateRow 12 13, 12258020302919476430276131200⟩, ⟨.privateRow 12 14, 19782603188397042361067700000⟩, ⟨.privateRow 13 7, 11509878218703733737348480⟩, ⟨.privateRow 13 8, 332964334183929440259009600⟩, ⟨.privateRow 13 9, 1215177527320836504193137600⟩, ⟨.privateRow 13 10, 2920631597996072435852176800⟩, ⟨.privateRow 13 11, 6686192892501532598332435200⟩, ⟨.privateRow 13 12, 1096315900331530638482442720⟩, ⟨.privateRow 14 6, 116377657544671085566523520⟩, ⟨.privateRow 14 7, 587825923312369258728868800⟩, ⟨.privateRow 14 8, 1611382950618522723228787200⟩, ⟨.privateRow 14 9, 1018304503515871998707080800⟩, ⟨.privateRow 15 4, 40914020230548428519480925⟩, ⟨.privateRow 15 5, 276396936668593828220493360⟩, ⟨.privateRow 15 6, 498761389477161795285100800⟩, ⟨.privateRow 16 3, 116897200658709795769945500⟩, ⟨.privateRow 16 4, 31172586842322612205318800⟩, ⟨.hall 7 26, 443083685756013351818378610000⟩, ⟨.hall 6 27, 2454974810633658522364021152000⟩, ⟨.hall 5 28, 10201046308296171573705235776000⟩, ⟨.hall 4 29, 23129710304030744243089850029440⟩, ⟨.hall 3 30, 22812529434023575162756293854400⟩, ⟨.hall 2 31, 41004966252660904740589942599000⟩, ⟨.assumptionRow 18, 81151417075033123821602600⟩]
  caps := #[0, 16928858613144821775520588980480, 0, 147365190510262618123216186200, 0, 7605602281327801535532427680, 3002079812978392740683705616, 2500458503042224592423641800, 0, 344095767079180490018969480, 0, 481069509582625734017280072, 0, 334325749113294975454377960, 3601854311612010169146133560, 81151417075033123821602600, 1794378546120150700062853500, 7305452730559698136780758400, 1003370692642642689362397400, 72301473981178387545600000, 0, 0, 0] }

theorem case_56_34_18_checked :
    (Witness.linear .conditional case_56_34_18).check 56 34 18 = true := by
  change case_56_34_18.check 56 34 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_34_19 : Certificate := {
  objectiveScale := 761220021409848000000
  eta := 55778836657383355937613192000
  rows := #[⟨.count 2, 10441358586111170076991632000⟩, ⟨.count 3, 1856241526419763569242956800⟩, ⟨.count 4, 354151343856402259921353600⟩, ⟨.count 5, 65881148358042162689544000⟩, ⟨.count 6, 12350746129293413569728000⟩, ⟨.count 7, 2536313937265611715212000⟩, ⟨.count 8, 632240575666210456545600⟩, ⟨.count 9, 198494134220787003799200⟩, ⟨.count 10, 65437626666193517736000⟩, ⟨.count 11, 26659773826967729448000⟩, ⟨.count 12, 7270847407354835304000⟩, ⟨.count 13, 9452101629561285895200⟩, ⟨.path 9, 8270896687579179108000⟩, ⟨.privateRow 2 32, 966792461676960192314040000⟩, ⟨.privateRow 3 29, 86502483413201701417572000⟩, ⟨.privateRow 3 30, 297161472431234080163894400⟩, ⟨.privateRow 4 27, 49250175540829080156939600⟩, ⟨.privateRow 4 28, 104070789642012944801450400⟩, ⟨.privateRow 4 29, 209855560379519669445230400⟩, ⟨.privateRow 5 24, 2856635159156299737216000⟩, ⟨.privateRow 5 25, 16682749329472790465341440⟩, ⟨.privateRow 5 26, 35832917277666834828703200⟩, ⟨.privateRow 5 27, 75212823211286075164449600⟩, ⟨.privateRow 6 22, 1662369619929191233632000⟩, ⟨.privateRow 6 23, 5571488793869180186004000⟩, ⟨.privateRow 6 24, 12136498492356691089436800⟩, ⟨.privateRow 6 25, 25806863032488299739978000⟩, ⟨.privateRow 6 26, 42401427754535664726912000⟩, ⟨.privateRow 6 27, 40213441266211292991912000⟩, ⟨.privateRow 7 20, 656724144470560176260250⟩, ⟨.privateRow 7 21, 1943869710127038259995000⟩, ⟨.privateRow 7 22, 4178616595401885139503000⟩, ⟨.privateRow 7 23, 9039359858403776411109600⟩, ⟨.privateRow 7 24, 15148962049211452581619500⟩, ⟨.privateRow 7 25, 22048339842844693973595000⟩, ⟨.privateRow 7 26, 22854394065143392520769000⟩, ⟨.privateRow 8 18, 217690069011686158487600⟩, ⟨.privateRow 8 19, 692661822541287982007625⟩, ⟨.privateRow 8 20, 1499733458557057362038400⟩, ⟨.privateRow 8 21, 3273315305992793090429400⟩, ⟨.privateRow 8 22, 5637600993600389402348760⟩, ⟨.privateRow 8 23, 8322509845234062499571550⟩, ⟨.privateRow 8 24, 10470565580146514450407800⟩, ⟨.privateRow 8 25, 8924884405334645281934400⟩, ⟨.privateRow 9 16, 64169267729577174244080⟩, ⟨.privateRow 9 17, 245404564530461533797600⟩, ⟨.privateRow 9 18, 561218534255201350027500⟩, ⟨.privateRow 9 19, 1246927248306092810714400⟩, ⟨.privateRow 9 20, 2206540613745362407312800⟩, ⟨.privateRow 9 21, 3343103323024387251288960⟩, ⟨.privateRow 9 22, 4314096718758930237334200⟩, ⟨.privateRow 9 23, 4413431305328856714103200⟩, ⟨.privateRow 9 24, 2133549384494861366233200⟩, ⟨.privateRow 10 14, 16921244875298525798400⟩, ⟨.privateRow 10 15, 84996206191978024703760⟩, ⟨.privateRow 10 16, 215863380805023554803200⟩, ⟨.privateRow 10 17, 502779098218586861271600⟩, ⟨.privateRow 10 18, 921943451252593116547200⟩, ⟨.privateRow 10 19, 1444596199051283194316400⟩, ⟨.privateRow 10 20, 1940007505230417155813280⟩, ⟨.privateRow 10 21, 1570139497618276683898800⟩, ⟨.privateRow 11 12, 3685915699561826230500⟩, ⟨.privateRow 11 13, 28422403501477992552000⟩, ⟨.privateRow 11 14, 83917697159887057467000⟩, ⟨.privateRow 11 15, 213076222632204201270000⟩, ⟨.privateRow 11 16, 415044206169838515270000⟩, ⟨.privateRow 11 17, 680603251952750833278000⟩, ⟨.privateRow 11 18, 962276457565058689053000⟩, ⟨.privateRow 11 19, 45079253925599978884800⟩, ⟨.privateRow 12 10, 372863969607940272000⟩, ⟨.privateRow 12 11, 8937083271540318394500⟩, ⟨.privateRow 12 12, 32388320269126084536000⟩, ⟨.privateRow 12 13, 93430389184509633656400⟩, ⟨.privateRow 12 14, 200419562330512450926000⟩, ⟨.privateRow 12 15, 352484623269056286508500⟩, ⟨.privateRow 12 16, 181424954354949223776000⟩, ⟨.privateRow 13 9, 2125324626765259550400⟩, ⟨.privateRow 13 10, 12118079012258058840000⟩, ⟨.privateRow 13 11, 41642126060304965832000⟩, ⟨.privateRow 13 12, 102300823021482532727280⟩, ⟨.privateRow 13 13, 134753038616309614300800⟩, ⟨.privateRow 14 7, 375083397998463726000⟩, ⟨.privateRow 14 8, 3796998090507525103200⟩, ⟨.privateRow 14 9, 18379086501924722574000⟩, ⟨.privateRow 14 10, 54039288104360482996800⟩, ⟨.privateRow 14 11, 16068572770254186021840⟩, ⟨.privateRow 15 6, 1050233514395698432800⟩, ⟨.privateRow 15 7, 7068879423817200990000⟩, ⟨.privateRow 15 8, 18838563664472840638350⟩, ⟨.privateRow 16 4, 262558378598924608200⟩, ⟨.privateRow 16 5, 2531812936489630150500⟩, ⟨.privateRow 16 6, 4241327654290320594000⟩, ⟨.privateRow 17 3, 700155676263798955200⟩, ⟨.privateRow 17 4, 750166795996927452000⟩, ⟨.hall 7 26, 8730066088414243222650000⟩, ⟨.hall 6 27, 30077937685496806187940000⟩, ⟨.hall 5 28, 85766776728893128532664000⟩, ⟨.hall 4 29, 276036655429273243607182080⟩, ⟨.hall 3 30, 264234720680402464785592800⟩, ⟨.hall 2 31, 455410133263620722168982000⟩, ⟨.assumptionRow 19, 669867529080494961216⟩]
  caps := #[0, 0, 0, 1059829120610488807881120, 0, 387038406241803930563040, 29214799744595209187040, 5707655373911975813901, 0, 0, 12264377275242410677632, 0, 3584125471227146290368, 0, 4766839452196794522576, 3193596106986420315180, 669867529080494961216, 669867529080494961216, 69118869290416767581760, 9987212770657377038784, 761220021409848000000, 0, 0] }

theorem case_56_34_19_checked :
    (Witness.linear .conditional case_56_34_19).check 56 34 19 = true := by
  change case_56_34_19.check 56 34 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_34_20 : Certificate := {
  objectiveScale := 8980902976019864088719520000
  eta := 683359328427366704185430672921006400
  rows := #[⟨.count 2, 127002974104865377168069108559270400⟩, ⟨.count 3, 22175236485391369870917948988827360⟩, ⟨.count 4, 4078673745663514196502529004338560⟩, ⟨.count 5, 709520862318798199428662658955200⟩, ⟨.count 6, 117425665647578763754571272780800⟩, ⟨.count 7, 19654343184857525088655750439400⟩, ⟨.count 8, 3632485869148585494933075988800⟩, ⟨.count 9, 934067794923921984411362397120⟩, ⟨.count 10, 307934437887007247608141449600⟩, ⟨.count 11, 141136617364878321820398164400⟩, ⟨.count 12, 51322406314501207934690241600⟩, ⟨.count 13, 66719128208851570315097314080⟩, ⟨.path 9, 103076484490265598469564898400⟩, ⟨.path 10, 1828059721868856227604652800⟩, ⟨.privateRow 2 32, 12499161478646253182830330819747200⟩, ⟨.privateRow 3 29, 1063147068298646822447637334093440⟩, ⟨.privateRow 3 30, 3721014739045263878566730669327040⟩, ⟨.privateRow 4 27, 585827305237821213151711966279440⟩, ⟨.privateRow 4 28, 1281674452892038665753019403476800⟩, ⟨.privateRow 4 29, 2679039874098225954432417549568320⟩, ⟨.privateRow 5 24, 33102571906880579108927541459840⟩, ⟨.privateRow 5 25, 192919100539541080583551829188032⟩, ⟨.privateRow 5 26, 431005568229181144235528648956800⟩, ⟨.privateRow 5 27, 948296266784165219295596853952320⟩, ⟨.privateRow 5 28, 1505998988403132945501335483928000⟩, ⟨.privateRow 6 22, 18755488263154941433021800513600⟩, ⟨.privateRow 6 23, 62295897116486966209022343998400⟩, ⟨.privateRow 6 24, 141948651882565540932609263333760⟩, ⟨.privateRow 6 25, 319047164476494384159555628302000⟩, ⟨.privateRow 6 26, 557747201037773627252615361518400⟩, ⟨.privateRow 6 27, 790769934004244111723492276990400⟩, ⟨.privateRow 7 20, 7141031691103644635287759397625⟩, ⟨.privateRow 7 21, 20929155098848081878604931262000⟩, ⟨.privateRow 7 22, 47245482662893018229378285532900⟩, ⟨.privateRow 7 23, 109019055493263465894869011206720⟩, ⟨.privateRow 7 24, 196341884482111011767897314591050⟩, ⟨.privateRow 7 25, 308084841049956688648061166835800⟩, ⟨.privateRow 7 26, 379937635512656004790181246471400⟩, ⟨.privateRow 8 17, 20757062109420488542474719936⟩, ⟨.privateRow 8 18, 2218411012944314712976985693160⟩, ⟨.privateRow 8 19, 7130375163681397509473542465515⟩, ⟨.privateRow 8 20, 16281320592076695700503608449800⟩, ⟨.privateRow 8 21, 38257860100425637944848718182040⟩, ⟨.privateRow 8 22, 71526241396299325956300075559464⟩, ⟨.privateRow 8 23, 115010340540962491281983756820390⟩, ⟨.privateRow 8 24, 159249910258649773138577924242320⟩, ⟨.privateRow 8 25, 160614254653550224000067668854780⟩, ⟨.privateRow 9 16, 612333332227904412003004238112⟩, ⟨.privateRow 9 17, 2373059362588905852812288418080⟩, ⟨.privateRow 9 18, 5802710845053174073793602510680⟩, ⟨.privateRow 9 19, 14006780788734458237896461524160⟩, ⟨.privateRow 9 20, 27170747193349164496283426554320⟩, ⟨.privateRow 9 21, 45235568925601364673635978946240⟩, ⟨.privateRow 9 22, 64715701053469110662024530843320⟩, ⟨.privateRow 9 23, 75988144872236838472576203899040⟩, ⟨.privateRow 9 24, 53323409911807705030721664464160⟩, ⟨.privateRow 10 14, 137170795058757773934535736640⟩, ⟨.privateRow 10 15, 760084837517762889512762478096⟩, ⟨.privateRow 10 16, 2093954177631649283735361857280⟩, ⟨.privateRow 10 17, 5374739001286139000960435551560⟩, ⟨.privateRow 10 18, 10900879101200056565328207315840⟩, ⟨.privateRow 10 19, 18903752992507944922610905656000⟩, ⟨.privateRow 10 20, 28236561506112274581507877123488⟩, ⟨.privateRow 10 21, 35393214454637895521960757863400⟩, ⟨.privateRow 10 22, 18450405070063184252521141855200⟩, ⟨.privateRow 11 12, 19958713566750469752379538400⟩, ⟨.privateRow 11 13, 221619481812618852445253316000⟩, ⟨.privateRow 11 14, 750590192349580166044844783400⟩, ⟨.privateRow 11 15, 2135582351642300263504610608800⟩, ⟨.privateRow 11 16, 4653231505848109519411915238400⟩, ⟨.privateRow 11 17, 8490803339912181984147503422800⟩, ⟨.privateRow 11 18, 13356656243348939365003135376400⟩, ⟨.privateRow 11 19, 16610496803688315948062496693840⟩, ⟨.privateRow 12 11, 50966000715094949546254892700⟩, ⟨.privateRow 12 12, 254279194921846893858238015200⟩, ⟨.privateRow 12 13, 863071799522195313435040896240⟩, ⟨.privateRow 12 14, 2097565754372299368738173392800⟩, ⟨.privateRow 12 15, 4129849883120019075994605378750⟩, ⟨.privateRow 12 16, 6919360137044359284051987930000⟩, ⟨.privateRow 12 17, 3517723266139770293856893643000⟩, ⟨.privateRow 13 9, 4737452890569342270894483840⟩, ⟨.privateRow 13 10, 72279055559589201174688756920⟩, ⟨.privateRow 13 11, 338727881675707972368955594560⟩, ⟨.privateRow 13 12, 981284408733263095711277419392⟩, ⟨.privateRow 13 13, 2160673305840500854050459171360⟩, ⟨.privateRow 13 14, 3003002299477251929278562761620⟩, ⟨.privateRow 14 8, 10264481262900241586938048320⟩, ⟨.privateRow 14 9, 116140704659852733511465694880⟩, ⟨.privateRow 14 10, 456251008054469829326473551840⟩, ⟨.privateRow 14 11, 1194272394938443108640241922032⟩, ⟨.privateRow 14 12, 549403191546962930866295166560⟩, ⟨.privateRow 15 7, 22952520601763040215236469160⟩, ⟨.privateRow 15 8, 190273069336354478306018266080⟩, ⟨.privateRow 15 9, 555487287132786937699181425560⟩, ⟨.privateRow 16 5, 1985688339549153878425515300⟩, ⟨.privateRow 16 6, 49183972718063657604078148200⟩, ⟨.privateRow 16 7, 187647548087395041511211195850⟩, ⟨.privateRow 17 4, 5295168905464410342468040800⟩, ⟨.privateRow 17 5, 57024895905001342149655824000⟩, ⟨.privateRow 18 3, 18003574278578995164391338720⟩, ⟨.hall 8 25, 28022033847717659532340871913600⟩, ⟨.hall 7 26, 163029425317740087094020196164000⟩, ⟨.hall 6 27, 443237408400803932126629823204800⟩, ⟨.hall 5 28, 978866749784463125015656666440000⟩, ⟨.hall 4 29, 1935441846384933432956594964683904⟩, ⟨.hall 3 30, 3521732594595212381769658283250240⟩, ⟨.hall 2 31, 5908367997808358185562038562782800⟩, ⟨.assumptionRow 20, 5153265155596546782989539344⟩]
  caps := #[0, 0, 61483465659692276430676296439680, 0, 5025740707940237245851071912640, 755977006553513918247889293024, 0, 0, 22245497091611985176654387355, 25444917334085005788575242608, 2527695091657152408998182176, 59700622514154197333898765456, 17249404385143030847031954900, 8316289585075530182059338480, 18260294322232470429536430816, 106225172183554308437853175512, 6478892490769776260249098032, 858777856551402925676919329664, 5153265155596546782989539344, 736135555663436113022903249184, 111598473532661686370364220656, 8980902976019864088719520000, 0] }

theorem case_56_34_20_checked :
    (Witness.linear .conditional case_56_34_20).check 56 34 20 = true := by
  change case_56_34_20.check 56 34 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_34_21 : Certificate := {
  objectiveScale := 17761133064159467840000000
  eta := 2913693587279315558951974853112000
  rows := #[⟨.count 2, 387445328766701440004395577952000⟩, ⟨.count 3, 60352060827120801231453926565600⟩, ⟨.count 4, 11739097443429218594727774979200⟩, ⟨.count 5, 2303446350402025557891690528000⟩, ⟨.count 6, 426440988002973334968761184000⟩, ⟨.count 7, 80736999921615565611775692000⟩, ⟨.count 8, 13965318905360530267982822400⟩, ⟨.count 9, 2057390731593292405551040800⟩, ⟨.count 10, 287746955467593343433712000⟩, ⟨.path 3, 3119299511421430324514367640800⟩, ⟨.path 10, 66602000856596052255408000⟩, ⟨.path 11, 18873333833907013203991248⟩, ⟨.privateRow 2 32, 39469482556275198669886451808000⟩, ⟨.privateRow 3 31, 62828972232438071352064147776000⟩, ⟨.privateRow 5 24, 85849304163756474013447975200⟩, ⟨.privateRow 5 25, 480614787590017725299977882560⟩, ⟨.privateRow 5 26, 1107032076531402927247486544400⟩, ⟨.privateRow 5 27, 2257989791544398673160290091200⟩, ⟨.privateRow 6 22, 52429322250992126813898096000⟩, ⟨.privateRow 6 23, 180108279533419537186286400000⟩, ⟨.privateRow 6 24, 409566227658996027561615273600⟩, ⟨.privateRow 6 25, 923747656760826741684280440000⟩, ⟨.privateRow 6 26, 1617303077794902282572395608000⟩, ⟨.privateRow 7 20, 21908483690119860890550619125⟩, ⟨.privateRow 7 21, 61977782482574993623932057000⟩, ⟨.privateRow 7 22, 139393417496585947578117234000⟩, ⟨.privateRow 7 23, 322402479416721616733509689000⟩, ⟨.privateRow 7 24, 590662072061684146392906287250⟩, ⟨.privateRow 7 25, 951205510337772575935132083000⟩, ⟨.privateRow 8 17, 552793873337187656440986720⟩, ⟨.privateRow 8 18, 7184703997028652435322181200⟩, ⟨.privateRow 8 19, 21538958650259828258366735850⟩, ⟨.privateRow 8 20, 47896679683228693653472336200⟩, ⟨.privateRow 8 21, 112801469109704630332968891000⟩, ⟨.privateRow 8 22, 214200352314563674928034446280⟩, ⟨.privateRow 8 23, 355306443686578230691732237350⟩, ⟨.privateRow 8 24, 514874153253882327727227806400⟩, ⟨.privateRow 9 15, 349510822171495955029332000⟩, ⟨.privateRow 9 16, 2313005943700337825634654960⟩, ⟨.privateRow 9 17, 7310548884651362240151060800⟩, ⟨.privateRow 9 18, 17054002718320662427326493500⟩, ⟨.privateRow 9 19, 40741086594018400694627608800⟩, ⟨.privateRow 9 20, 80272874739740984496718723200⟩, ⟨.privateRow 9 21, 137795302877802874992391223520⟩, ⟨.privateRow 9 22, 206663859902318144717195204400⟩, ⟨.privateRow 9 23, 261011533251527490063157125600⟩, ⟨.privateRow 9 24, 128005032436857419919107432400⟩, ⟨.privateRow 10 13, 145072423381578310647829800⟩, ⟨.privateRow 10 14, 772992957642489390769653600⟩, ⟨.privateRow 10 15, 2499082308236048187721788720⟩, ⟨.privateRow 10 16, 6170573600582835031411824000⟩, ⟨.privateRow 10 17, 15455608345553107459183255800⟩, ⟨.privateRow 10 18, 31555564337814004298127002400⟩, ⟨.privateRow 10 19, 56328864424076960255011071600⟩, ⟨.privateRow 10 20, 87797351052272080948494205440⟩, ⟨.privateRow 10 21, 116911588006483175437117185600⟩, ⟨.privateRow 10 22, 120086396081808955326335808000⟩, ⟨.privateRow 11 11, 49802357677083463286604000⟩, ⟨.privateRow 11 13, 1420205617326795933689874000⟩, ⟨.privateRow 11 14, 2034610764285441265862538600⟩, ⟨.privateRow 11 15, 6109294156362884597162052000⟩, ⟨.privateRow 11 16, 13269330956823288868552531500⟩, ⟨.privateRow 11 17, 24785632098640138528745514000⟩, ⟨.privateRow 11 18, 40668236372753192538631296000⟩, ⟨.privateRow 11 19, 58031367243926887536993867600⟩, ⟨.privateRow 11 20, 46132431162518011966544389500⟩, ⟨.privateRow 12 9, 15415015471478214826806000⟩, ⟨.privateRow 12 10, 44268762379629745143648000⟩, ⟨.privateRow 12 11, 185836575406154034300939000⟩, ⟨.privateRow 12 12, 1339549273748758405606182000⟩, ⟨.privateRow 12 13, 2293583024206275274952879400⟩, ⟨.privateRow 12 14, 5922791500041296319010572000⟩, ⟨.privateRow 12 15, 11821604087126959859401668000⟩, ⟨.privateRow 12 16, 20495119459078702068617844000⟩, ⟨.privateRow 12 17, 31250518309428418735832097000⟩, ⟨.privateRow 12 18, 11907928173767237862431781600⟩, ⟨.privateRow 13 7, 4795782591126555723895200⟩, ⟨.privateRow 13 8, 22608689358168048412648800⟩, ⟨.privateRow 13 9, 68616581688426104972654400⟩, ⟨.privateRow 13 10, 223003890487384841161126800⟩, ⟨.privateRow 13 11, 1572144729418396358215099200⟩, ⟨.privateRow 13 12, 2489011164794682420701608800⟩, ⟨.privateRow 13 13, 5852453355371440168393442400⟩, ⟨.privateRow 13 14, 10894819101391752965758920600⟩, ⟨.privateRow 13 15, 372015706711674251153584800⟩, ⟨.privateRow 14 5, 1298857785096775508554950⟩, ⟨.privateRow 14 6, 9698138128722590463876960⟩, ⟨.privateRow 14 7, 34141404636829527653444400⟩, ⟨.privateRow 14 8, 95915651822531114477904000⟩, ⟨.privateRow 14 9, 339434834505290666235693600⟩, ⟨.privateRow 14 10, 2030941263969503522467740000⟩, ⟨.privateRow 14 12, 13143286244925948790568489600⟩, ⟨.privateRow 14 17, 11118222640428398353230372000⟩, ⟨.privateRow 15 4, 4546002247838714279942325⟩, ⟨.privateRow 15 5, 16971741725264533311784680⟩, ⟨.privateRow 15 6, 54552026974064571359307900⟩, ⟨.privateRow 15 7, 167852390689429450336332000⟩, ⟨.privateRow 15 8, 542489601575419904073117450⟩, ⟨.privateRow 15 9, 2896216704804882697621437600⟩, ⟨.privateRow 15 10, 600072296714710284952386900⟩, ⟨.privateRow 15 11, 14882601136702208616024518200⟩, ⟨.privateRow 15 13, 254576125878967999676770200⟩, ⟨.privateRow 16 3, 9741433388225816314162125⟩, ⟨.privateRow 16 4, 31172586842322612205318800⟩, ⟨.privateRow 16 5, 111330667294009329304710000⟩, ⟨.privateRow 16 6, 323715324901042511362926000⟩, ⟨.privateRow 16 7, 974143338822581631416212500⟩, ⟨.privateRow 16 8, 4746734814626397767628090000⟩, ⟨.privateRow 16 9, 2135322198699098936064337800⟩, ⟨.privateRow 16 10, 19474207724550987458267217000⟩, ⟨.privateRow 16 11, 3516657453149519689412527125⟩, ⟨.privateRow 17 2, 25977155701935510171099000⟩, ⟨.privateRow 17 3, 83126898246193632547516800⟩, ⟨.privateRow 17 4, 29688177945069154481256000⟩, ⟨.privateRow 17 5, 1198945647781638930973800000⟩, ⟨.privateRow 17 6, 1835719002936776052090996000⟩, ⟨.privateRow 17 7, 9200636237703704329691064000⟩, ⟨.privateRow 17 8, 6712497033380135828211981600⟩, ⟨.privateRow 17 9, 30941678791638741003797920000⟩, ⟨.privateRow 17 10, 24028869024290346908266575000⟩, ⟨.privateRow 18 0, 41563449123096816273758400⟩, ⟨.privateRow 18 1, 88322329386580734581736600⟩, ⟨.privateRow 18 2, 235526211697548625551297600⟩, ⟨.privateRow 18 3, 100939805013235125236270400⟩, ⟨.privateRow 18 4, 3152427756567189295840444800⟩, ⟨.privateRow 18 5, 5122695104421682605740722800⟩, ⟨.privateRow 18 6, 21711234423755846028092342400⟩, ⟨.privateRow 18 7, 22610516322964668052924569600⟩, ⟨.privateRow 19 0, 596175723359419958426722050⟩, ⟨.privateRow 19 1, 847894362111175051984671360⟩, ⟨.privateRow 19 2, 454229122559558063563216800⟩, ⟨.privateRow 19 3, 10272566310193082360583518400⟩, ⟨.privateRow 19 4, 18547689171181954262164686000⟩, ⟨.privateRow 19 5, 66193571223906506899257866400⟩, ⟨.privateRow 20 0, 9397495846732190159496774240⟩, ⟨.privateRow 20 2, 10843264438537142491727047200⟩, ⟨.privateRow 20 3, 157743680284433191962981567600⟩, ⟨.privateRow 20 4, 245311255219892236631019691200⟩, ⟨.privateRow 20 5, 155058681471081137631696774960⟩, ⟨.privateRow 21 0, 172607066572632064154022384000⟩, ⟨.privateRow 21 9, 14982293378504463168569142931200⟩, ⟨.hall 18 7, 108673523465516645102493390⟩, ⟨.hall 19 8, 688461234192834443919177600⟩, ⟨.hall 12 9, 296499340647571404802680⟩, ⟨.hall 20 13, 345214133145264128308044768000⟩, ⟨.hall 9 15, 23848922886746163255504⟩, ⟨.hall 8 25, 266974822471227188408280590400⟩, ⟨.hall 7 26, 1262818811086290310777578654000⟩, ⟨.hall 6 27, 3002944355054772441201803772000⟩, ⟨.hall 5 28, 6371146458288826561594014768000⟩, ⟨.hall 4 29, 13113958151592488941520919589440⟩, ⟨.hall 3 30, 30738256173146578766628653935200⟩]
  caps := #[0, 430495544848124658149356000320, 18498301180017672408422467440, 17817312758419291462914769200, 7419255404229743110551715200, 1157054300323910544262731024, 0, 324245017130864078421250650, 16756103235394121051035440, 96746369364739299628297264, 146071355033742393259826432, 44494691715758654943538248, 117190460841974323103091000, 0, 575019115470526095364844030, 0, 229020317379518201663849125, 1576708609444065711563495000, 8727948430579277167054355400, 0, 652855343793373182238743584800, 0, 17761133064159467840000000] }

theorem case_56_34_21_checked :
    (Witness.linear .conditional case_56_34_21).check 56 34 21 = true := by
  change case_56_34_21.check 56 34 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_34_22 : Certificate := {
  objectiveScale := 12552339232843470060000000
  eta := 2448517542866072146056884528232000
  rows := #[⟨.count 2, 249302139819738244659792996624000⟩, ⟨.count 3, 30870773856515244673946903378400⟩, ⟨.count 4, 5481637051048746711080900342400⟩, ⟨.count 5, 1059867952638968814980839200000⟩, ⟨.count 6, 192023134948707291184763808000⟩, ⟨.count 7, 32185695914698097101991661000⟩, ⟨.count 8, 4946050445648521136577249600⟩, ⟨.count 9, 561106563161807019695738400⟩, ⟨.path 3, 3776774685778086795450042595200⟩, ⟨.path 10, 49310919538166188702800000⟩, ⟨.privateRow 2 32, 27386987896190954179104884928000⟩, ⟨.privateRow 3 31, 42590793676796961830005023252000⟩, ⟨.privateRow 6 22, 14428454481303609077890416000⟩, ⟨.privateRow 6 23, 66362973766544583317100912000⟩, ⟨.privateRow 7 20, 6653399004158232542572731375⟩, ⟨.privateRow 7 21, 24459347604493849648244787000⟩, ⟨.privateRow 7 22, 64033688805271032571759035000⟩, ⟨.privateRow 7 25, 1198456078308794761743652365000⟩, ⟨.privateRow 7 27, 3376380812359067934488592525000⟩, ⟨.privateRow 8 17, 7273603596541942847907720⟩, ⟨.privateRow 8 18, 2254817114928002282851393200⟩, ⟨.privateRow 8 19, 7955503933717749989899068750⟩, ⟨.privateRow 8 20, 21067473274269698748761289000⟩, ⟨.privateRow 8 21, 58037295364074252307263682500⟩, ⟨.privateRow 8 23, 300017964348363787619073680700⟩, ⟨.privateRow 9 15, 30227962998615866380915200⟩, ⟨.privateRow 9 16, 633842599127226448174815600⟩, ⟨.privateRow 9 17, 2498425108399486400455921600⟩, ⟨.privateRow 9 18, 6819003371758071419913487500⟩, ⟨.privateRow 9 19, 19493257638732406832392689600⟩, ⟨.privateRow 9 20, 45723257656166755969157053200⟩, ⟨.privateRow 9 21, 47581836556121235270198616320⟩, ⟨.privateRow 9 22, 166804512193268297910660898800⟩, ⟨.privateRow 9 25, 1112923695444601900954291797600⟩, ⟨.privateRow 10 13, 14387347773379667171685600⟩, ⟨.privateRow 10 14, 171340232573885127226437600⟩, ⟨.privateRow 10 15, 748142084215742692927651200⟩, ⟨.privateRow 10 16, 2223644528085679670646074400⟩, ⟨.privateRow 10 17, 6655946763659768525301050700⟩, ⟨.privateRow 10 18, 16461181188142536339718567200⟩, ⟨.privateRow 10 19, 35323336674942646184350095600⟩, ⟨.privateRow 10 20, 49135670115646239324740661120⟩, ⟨.privateRow 10 21, 100215070915476071684376046800⟩, ⟨.privateRow 10 22, 97028273383672475405847686400⟩, ⟨.privateRow 11 11, 4611329414544765119130000⟩, ⟨.privateRow 11 12, 45959583164962825687329000⟩, ⟨.privateRow 11 13, 219080068367372204659758000⟩, ⟨.privateRow 11 14, 716969497373420080722332400⟩, ⟨.privateRow 11 15, 2333947527681590452295664000⟩, ⟨.privateRow 11 16, 6150591173119807715895594000⟩, ⟨.privateRow 11 17, 13966004017159262633086236000⟩, ⟨.privateRow 11 18, 27815539028534023198592160000⟩, ⟨.privateRow 11 19, 41915139846446097026844048000⟩, ⟨.privateRow 11 21, 222724136502902458743899580000⟩, ⟨.privateRow 12 9, 856389748415456379267000⟩, ⟨.privateRow 12 10, 12911722360725342333564000⟩, ⟨.privateRow 12 11, 63943767881687409651936000⟩, ⟨.privateRow 12 12, 229979574256296194941338000⟩, ⟨.privateRow 12 13, 827272496969330862371922000⟩, ⟨.privateRow 12 14, 2399223457394146349648682000⟩, ⟨.privateRow 12 15, 5828374530278492253196385250⟩, ⟨.privateRow 12 16, 12290905669258629955239984000⟩, ⟨.privateRow 12 18, 80511598139832617492752617600⟩, ⟨.privateRow 12 19, 1702502819849927281982796000⟩, ⟨.privateRow 12 20, 60742583002110433706235954000⟩, ⟨.privateRow 12 21, 89027709076025598819459519000⟩, ⟨.privateRow 13 8, 3083003094295642965361200⟩, ⟨.privateRow 13 9, 18814224011342641686050400⟩, ⟨.privateRow 13 10, 74334630162461613720375600⟩, ⟨.privateRow 13 11, 295594599707618616436449600⟩, ⟨.privateRow 13 12, 962513566039099733785766640⟩, ⟨.privateRow 13 13, 2567342280449749497525230400⟩, ⟨.privateRow 13 14, 5774721712540263911035307700⟩, ⟨.privateRow 13 15, 11310510685272615492255122400⟩, ⟨.privateRow 13 16, 5817284283036512093084877600⟩, ⟨.privateRow 13 17, 39660162872098390525468524960⟩, ⟨.privateRow 13 18, 43151252809308966764678035800⟩, ⟨.privateRow 14 6, 1385448304103227209125280⟩, ⟨.privateRow 14 7, 5937635589013830896251200⟩, ⟨.privateRow 14 8, 23978912955632778619476000⟩, ⟨.privateRow 14 9, 109104053948129142718615800⟩, ⟨.privateRow 14 10, 398631262044246737898319200⟩, ⟨.privateRow 14 11, 1207418197025962512752681520⟩, ⟨.privateRow 14 12, 3015659141931357891862692800⟩, ⟨.privateRow 14 13, 6431943751799232318364112400⟩, ⟨.privateRow 14 14, 12086057241437652789319317600⟩, ⟨.privateRow 14 15, 11190958676393817781709449200⟩, ⟨.privateRow 14 16, 27203277451066866251174872800⟩, ⟨.privateRow 15 5, 2424534532180647615969240⟩, ⟨.privateRow 15 6, 7793146710580653051329700⟩, ⟨.privateRow 15 7, 41963097672357362584083000⟩, ⟨.privateRow 15 8, 172748085417871142637808350⟩, ⟨.privateRow 15 9, 595113021535249869374268000⟩, ⟨.privateRow 15 10, 1683839232599459769290637180⟩, ⟨.privateRow 15 11, 3988359305437165328269399800⟩, ⟨.privateRow 15 12, 8146436028126975989656646400⟩, ⟨.privateRow 15 14, 46963233888339144321324178800⟩, ⟨.privateRow 15 15, 10983141430778333700340657200⟩, ⟨.privateRow 16 4, 5195431140387102034219800⟩, ⟨.privateRow 16 5, 16699600094101399395706500⟩, ⟨.privateRow 16 6, 77931467105806530513297000⟩, ⟨.privateRow 16 7, 311725868423226122053188000⟩, ⟨.privateRow 16 8, 1006024393547684302989834000⟩, ⟨.privateRow 16 9, 2712015055282067261862735600⟩, ⟨.privateRow 16 10, 6165244953259361080607496000⟩, ⟨.privateRow 16 11, 12235240335611625290587629000⟩, ⟨.privateRow 16 12, 6980432839334384947405317000⟩, ⟨.privateRow 16 13, 40043785514533588928749108500⟩, ⟨.privateRow 16 15, 95407598604283644980903852250⟩, ⟨.privateRow 17 3, 13854483041032272091252800⟩, ⟨.privateRow 17 4, 44532266917603731721884000⟩, ⟨.privateRow 17 5, 175845361674640376542824000⟩, ⟨.privateRow 17 6, 658087944449032924334508000⟩, ⟨.privateRow 17 7, 2021495025532436064223704000⟩, ⟨.privateRow 17 8, 5216212864948650442356679200⟩, ⟨.privateRow 17 9, 11545402534193560076044000000⟩, ⟨.privateRow 17 11, 67273411223526704054526096000⟩, ⟨.privateRow 17 12, 26600607438781962415205376000⟩, ⟨.privateRow 17 17, 1053009983533657840295669064000⟩, ⟨.privateRow 18 2, 47105242339509725110259520⟩, ⟨.privateRow 18 3, 100939805013235125236270400⟩, ⟨.privateRow 18 4, 489169824294908683837310400⟩, ⟨.privateRow 18 5, 1707565034807227535246907600⟩, ⟨.privateRow 18 6, 5010284867020579852636694400⟩, ⟨.privateRow 18 7, 12506441841139832016773902560⟩, ⟨.privateRow 18 8, 27007005607985575729882124800⟩, ⟨.privateRow 18 9, 16074663948357693693876061200⟩, ⟨.privateRow 18 10, 94075898272335136720204012800⟩, ⟨.privateRow 18 11, 152385458968313960731689547200⟩, ⟨.privateRow 19 1, 211973590527793762996167840⟩, ⟨.privateRow 19 2, 454229122559558063563216800⟩, ⟨.privateRow 19 3, 1712094385032180393430586400⟩, ⟨.privateRow 19 4, 5564306751354586278649405800⟩, ⟨.privateRow 19 5, 15898019289584532224712588000⟩, ⟨.privateRow 19 6, 38791167066586258628298714720⟩, ⟨.privateRow 19 7, 82669700305839567568505457600⟩, ⟨.privateRow 19 8, 86246754645996087319065789900⟩, ⟨.privateRow 19 9, 200769272171324664094941825600⟩, ⟨.privateRow 19 13, 1870666936407779958441181188000⟩, ⟨.privateRow 20 0, 1342499406676027165642396320⟩, ⟨.privateRow 20 1, 1438392221438600534616853200⟩, ⟨.privateRow 20 2, 7745188884669387494090748000⟩, ⟨.privateRow 20 3, 25171863875175509355794931000⟩, ⟨.privateRow 20 4, 69565878345939589492378718400⟩, ⟨.privateRow 20 6, 682437198393647142534884796000⟩, ⟨.privateRow 20 14, 36509271364554558769644967922400⟩, ⟨.privateRow 21 0, 28767844428772010692337064000⟩, ⟨.privateRow 21 13, 83771962976584095136085530368000⟩, ⟨.hall 17 11, 37624056280385716929130200⟩, ⟨.hall 12 12, 297783118737166031222400⟩, ⟨.hall 14 13, 1095383469536723370063060⟩, ⟨.hall 12 17, 689482527910880989240800⟩, ⟨.hall 9 18, 1009354817919824627839848⟩, ⟨.hall 13 19, 895098565043835007609868400⟩, ⟨.hall 6 21, 6133510767307537388268000⟩, ⟨.hall 8 25, 21988663180315257994059492000⟩, ⟨.hall 5 28, 9672452394905311149773987352000⟩, ⟨.hall 4 29, 15329082172607933764830873517440⟩, ⟨.hall 3 30, 20920254867097478162667761364000⟩]
  caps := #[0, 0, 38662706898007350466144636800, 0, 0, 0, 1357367851386835932854496000, 0, 326581620401272853105178690, 67383051601509963380661600, 78070964280122095245854820, 297476660907632817542214000, 0, 97985220715129092973191600, 263646209755774041536623400, 10217681242761300667298940, 487969148566827215701530000, 626502167978916930219688000, 18955018810060878805176887360, 847894362111175051984671360, 0, 0, 138075731561278170660000000] }

theorem case_56_34_22_checked :
    (Witness.linear .conditional case_56_34_22).check 56 34 22 = true := by
  change case_56_34_22.check 56 34 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_35_1_checked :
    (Witness.rising).check 56 35 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_35_2_checked :
    (Witness.rising).check 56 35 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_35_3_checked :
    (Witness.rising).check 56 35 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_35_4_checked :
    (Witness.rising).check 56 35 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_35_5_checked :
    (Witness.rising).check 56 35 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_35_6_checked :
    (Witness.rising).check 56 35 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_35_7_checked :
    (Witness.rising).check 56 35 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_35_8_checked :
    (Witness.rising).check 56 35 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_35_9_checked :
    (Witness.rising).check 56 35 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_35_10_checked :
    (Witness.rising).check 56 35 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_35_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_35_11_checked :
    (Witness.linear .positive case_56_35_11).check 56 35 11 = true := by
  change case_56_35_11.check 56 35 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_35_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_35_12_checked :
    (Witness.linear .positive case_56_35_12).check 56 35 12 = true := by
  change case_56_35_12.check 56 35 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_35_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_35_13_checked :
    (Witness.linear .positive case_56_35_13).check 56 35 13 = true := by
  change case_56_35_13.check 56 35 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_35_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_35_14_checked :
    (Witness.linear .positive case_56_35_14).check 56 35 14 = true := by
  change case_56_35_14.check 56 35 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_35_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_35_15_checked :
    (Witness.linear .positive case_56_35_15).check 56 35 15 = true := by
  change case_56_35_15.check 56 35 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_35_16 : Certificate := {
  objectiveScale := 982010655208440000000
  eta := 216266593692368485573555248000
  rows := #[⟨.count 2, 40584929509601935541829345600⟩, ⟨.count 3, 7431363687023311929288595200⟩, ⟨.count 4, 1334863383666174461020521600⟩, ⟨.count 5, 254132307511596340274448000⟩, ⟨.count 6, 46912194536776878603294000⟩, ⟨.count 7, 8766122165712185421747600⟩, ⟨.count 8, 1652253392490254843889600⟩, ⟨.count 9, 326819352360709749340800⟩, ⟨.count 10, 60522102289020323952000⟩, ⟨.count 11, 15130525572255080988000⟩, ⟨.path 10, 7447680453777494112000⟩, ⟨.path 11, 1550710255526957196672⟩, ⟨.privateRow 2 33, 3900930920303003823212776800⟩, ⟨.privateRow 4 29, 881140614758043685080235200⟩, ⟨.privateRow 4 31, 2722113690372020097448495200⟩, ⟨.privateRow 5 29, 1701742315531986762785150400⟩, ⟨.privateRow 6 22, 3200421377814704943149250⟩, ⟨.privateRow 6 23, 9464864246663279590422000⟩, ⟨.privateRow 6 24, 18246363109197109957570500⟩, ⟨.privateRow 6 27, 254853529230540499134876000⟩, ⟨.privateRow 7 19, 217677827899509765147360⟩, ⟨.privateRow 7 20, 2104656107100681765430800⟩, ⟨.privateRow 7 21, 4648601806649169382213200⟩, ⟨.privateRow 7 26, 264773606146563338733308400⟩, ⟨.privateRow 8 17, 255705882171110868697200⟩, ⟨.privateRow 8 18, 953979637330682856293400⟩, ⟨.privateRow 8 20, 6967575504095189263555275⟩, ⟨.privateRow 8 21, 668300904502152398591400⟩, ⟨.privateRow 8 22, 4315856331772659726152100⟩, ⟨.privateRow 8 23, 6695560176234318438809760⟩, ⟨.privateRow 8 24, 10162669676031329396940000⟩, ⟨.privateRow 9 14, 13501084356781456881600⟩, ⟨.privateRow 9 15, 151977723525762146812800⟩, ⟨.privateRow 9 16, 428056323462343745769600⟩, ⟨.privateRow 9 17, 566083396743303430031040⟩, ⟨.privateRow 9 18, 1000856247112873134984000⟩, ⟨.privateRow 9 19, 3968232506750099240452800⟩, ⟨.privateRow 9 20, 1527750782067127320331200⟩, ⟨.privateRow 9 21, 3739593453658244683300800⟩, ⟨.privateRow 9 22, 5424797768505855036897600⟩, ⟨.privateRow 9 23, 7573836750618485039893200⟩, ⟨.privateRow 9 24, 6381719452475587492272000⟩, ⟨.privateRow 10 12, 14265924110983362074400⟩, ⟨.privateRow 10 13, 78213178342733957107200⟩, ⟨.privateRow 10 14, 204388182938545719012900⟩, ⟨.privateRow 10 15, 354466949088194033691600⟩, ⟨.privateRow 10 16, 500366480674475528273160⟩, ⟨.privateRow 10 17, 791998955232152072605200⟩, ⟨.privateRow 10 18, 2955748170540030071005800⟩, ⟨.privateRow 10 19, 1334512355472898143141600⟩, ⟨.privateRow 10 20, 2597154714477584651590200⟩, ⟨.privateRow 10 21, 3623760874555091896626000⟩, ⟨.privateRow 10 22, 4622375562323927241834000⟩, ⟨.privateRow 10 23, 4448878869095402313171600⟩, ⟨.privateRow 11 10, 10087017048170053992000⟩, ⟨.privateRow 11 11, 41658070406728274928000⟩, ⟨.privateRow 11 12, 106019486876920217832000⟩, ⟨.privateRow 11 13, 200479463832379823091000⟩, ⟨.privateRow 11 14, 309362977402967523672000⟩, ⟨.privateRow 11 15, 181703857099536018046800⟩, ⟨.privateRow 11 16, 1207385373947627674800000⟩, ⟨.privateRow 11 17, 2023191981917335658929500⟩, ⟨.privateRow 11 18, 1271160648401534011836000⟩, ⟨.privateRow 11 19, 1868619908173502502018000⟩, ⟨.privateRow 11 20, 2657470491417892406256000⟩, ⟨.privateRow 11 21, 3499277914165175093952000⟩, ⟨.privateRow 11 24, 24174453357489368033100000⟩, ⟨.privateRow 12 8, 6430473368208409419900⟩, ⟨.privateRow 12 9, 24511451427053231200560⟩, ⟨.privateRow 12 10, 61494778932951007729800⟩, ⟨.privateRow 12 11, 121626147869281227942000⟩, ⟨.privateRow 12 13, 697792329345909325928400⟩, ⟨.privateRow 12 15, 1113438565167171126483600⟩, ⟨.privateRow 12 16, 1773675860207601868818300⟩, ⟨.privateRow 12 17, 1337538460587349159339200⟩, ⟨.privateRow 12 19, 5253015868175519017413840⟩, ⟨.privateRow 12 22, 8249162541993470154657600⟩, ⟨.privateRow 13 6, 4153477608070022232000⟩, ⟨.privateRow 13 7, 16139227277072086387200⟩, ⟨.privateRow 13 8, 40886042435249285514240⟩, ⟨.privateRow 13 9, 83434041012720875162400⟩, ⟨.privateRow 13 10, 123682347498331277409600⟩, ⟨.privateRow 13 11, 2017403409634010798400⟩, ⟨.privateRow 13 12, 854095243515053480740800⟩, ⟨.privateRow 13 14, 1110916810905128612985600⟩, ⟨.privateRow 13 15, 1817680472080243729358400⟩, ⟨.privateRow 13 17, 3811547508601857735110400⟩, ⟨.privateRow 13 18, 1266122379886305177075840⟩, ⟨.privateRow 13 22, 25193333779509526850419200⟩, ⟨.privateRow 14 4, 2731900450546056289500⟩, ⟨.privateRow 14 5, 11956081971801563996400⟩, ⟨.privateRow 14 6, 31963235271388858587150⟩, ⟨.privateRow 14 7, 67532579137498511476440⟩, ⟨.privateRow 14 8, 120828054212722718175600⟩, ⟨.privateRow 14 9, 171479289818890917864000⟩, ⟨.privateRow 14 10, 5463800901092112579000⟩, ⟨.privateRow 14 11, 1178690867117416649997000⟩, ⟨.privateRow 14 13, 1487975112064085325681000⟩, ⟨.privateRow 14 14, 2137438912507234440904800⟩, ⟨.privateRow 14 15, 934778279878273432087200⟩, ⟨.privateRow 14 17, 1898124433039399909944600⟩, ⟨.privateRow 14 21, 35093993187714639094917000⟩, ⟨.privateRow 15 2, 2070492973045432135200⟩, ⟨.privateRow 15 3, 10199095015371943480800⟩, ⟨.privateRow 15 4, 29311684834094156894400⟩, ⟨.privateRow 15 5, 64746040677941534061150⟩, ⟨.privateRow 15 6, 122826244256550690775920⟩, ⟨.privateRow 15 7, 205126696686715312251600⟩, ⟨.privateRow 15 8, 314210581050497181850800⟩, ⟨.privateRow 15 10, 1835837102766949826544000⟩, ⟨.privateRow 15 12, 2485665156603505082606400⟩, ⟨.privateRow 15 14, 7069846148818845556507200⟩, ⟨.privateRow 16 0, 1639140270327633773700⟩, ⟨.privateRow 16 1, 10352464865227160676000⟩, ⟨.privateRow 16 2, 31872171923037323377500⟩, ⟨.privateRow 16 4, 301192024672702705917375⟩, ⟨.privateRow 16 5, 191233031538223940265000⟩, ⟨.privateRow 16 7, 1438660806495253950609000⟩, ⟨.privateRow 16 9, 3178441996917129853911000⟩, ⟨.privateRow 16 10, 945783935979044687424900⟩, ⟨.privateRow 16 11, 3748167418149189229194000⟩, ⟨.privateRow 16 12, 2040729636557904048256500⟩, ⟨.privateRow 16 13, 8076278274800012693559000⟩, ⟨.privateRow 17 0, 71777089732241647353600⟩, ⟨.privateRow 17 2, 178955549513416957881600⟩, ⟨.privateRow 17 3, 783509049216608943828600⟩, ⟨.privateRow 17 4, 573480542578628136291840⟩, ⟨.privateRow 17 6, 3740265921461456020233600⟩, ⟨.privateRow 17 8, 8144440965002468321395200⟩, ⟨.privateRow 17 9, 3865748413540691491894080⟩, ⟨.privateRow 17 10, 7739656103093680538572800⟩, ⟨.privateRow 17 11, 7926882347304436929613200⟩, ⟨.privateRow 17 13, 35580271467911837114448000⟩, ⟨.privateRow 18 0, 668769230293674579669600⟩, ⟨.privateRow 18 1, 340941176228147824929600⟩, ⟨.privateRow 18 3, 564738461136880756165440⟩, ⟨.privateRow 18 5, 51443786945667275359200⟩, ⟨.privateRow 18 9, 173384615261323039173600⟩, ⟨.privateRow 18 11, 4171846150879589044605600⟩, ⟨.privateRow 19 0, 7317122166742557165796800⟩, ⟨.privateRow 19 8, 297230769019410924297600⟩, ⟨.privateRow 19 10, 8598461532347244595752000⟩, ⟨.privateRow 20 0, 89740471090032457659414450⟩, ⟨.privateRow 20 6, 2541323075115963402744480⟩, ⟨.privateRow 20 7, 2823692305684403780827200⟩, ⟨.hall 18 2, 668769230293674579669600⟩, ⟨.hall 17 3, 24040723964805295347600⟩, ⟨.hall 19 3, 816853845572988236596440⟩, ⟨.hall 14 6, 134722202669564474250⟩, ⟨.hall 18 6, 13077097101734748568200⟩, ⟨.hall 19 6, 190408821811885369836000⟩, ⟨.hall 12 7, 7439039808405004800⟩, ⟨.hall 15 9, 428620151659857557400⟩, ⟨.hall 16 12, 1747791705250518127200⟩, ⟨.hall 14 14, 91739980042072932570⟩, ⟨.hall 18 16, 4956760177470764531668800⟩, ⟨.hall 9 17, 12068069683464593568⟩, ⟨.hall 17 17, 9957230762150265963969600⟩, ⟨.hall 8 20, 57623221383151012160⟩, ⟨.hall 5 23, 1204718523974201613520⟩, ⟨.hall 6 24, 7631515771665603246000⟩, ⟨.hall 10 24, 1953653461889576057170560⟩, ⟨.hall 2 32, 3711871885472407151887392000⟩]
  caps := #[0, 89000196949851189718510080, 0, 0, 546966148392930820226400, 0, 7690341354769646817660, 0, 33297124324235868917145, 7444208226052170189120, 3677128238781222126720, 1438924583376927826872, 16460235732962757740400, 1964021310416880000000, 2707409910057273156450, 311489519786287155464580, 8220180336104591712000, 11042629189575638054400, 0, 63111583665529122098232000, 0, 0] }

theorem case_56_35_16_checked :
    (Witness.linear .positive case_56_35_16).check 56 35 16 = true := by
  change case_56_35_16.check 56 35 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_35_17 : Certificate := {
  objectiveScale := 17508630662827375500000
  eta := 6083098654975598735611897564800
  rows := #[⟨.count 2, 918725842365762149235426349440⟩, ⟨.count 3, 145270098460613602695686987520⟩, ⟨.count 4, 22754819625158195646697866240⟩, ⟨.count 5, 3801991920870226974684393600⟩, ⟨.count 6, 635082281952160006728363600⟩, ⟨.count 7, 117834543880280290405021680⟩, ⟨.count 8, 26525525029327164939658560⟩, ⟨.count 9, 7533876931406532053867520⟩, ⟨.count 10, 2354336541064541266833600⟩, ⟨.count 11, 784778847021513755611200⟩, ⟨.count 12, 470867308212908253366720⟩, ⟨.path 2, 20216026547632152784910563200⟩, ⟨.path 8, 1799307570214018627963200⟩, ⟨.privateRow 2 33, 90620375412691747144814292000⟩, ⟨.privateRow 3 32, 148391948714065184415508341120⟩, ⟨.privateRow 6 23, 237503041185207284979406200⟩, ⟨.privateRow 6 24, 316620115801450587914888100⟩, ⟨.privateRow 6 25, 708792635158655686224145560⟩, ⟨.privateRow 6 28, 9032068799048540657939026500⟩, ⟨.privateRow 7 20, 17211362750510717421673040⟩, ⟨.privateRow 7 21, 80554278734895797372841300⟩, ⟨.privateRow 7 22, 173849068346973003180527760⟩, ⟨.privateRow 7 23, 289485297195060886601081400⟩, ⟨.privateRow 7 24, 601211226914711473036184208⟩, ⟨.privateRow 7 26, 1830091191606719719522724880⟩, ⟨.privateRow 7 27, 832493400920421791952360960⟩, ⟨.privateRow 8 18, 9641008135659296487683592⟩, ⟨.privateRow 8 19, 30115161607370014895880160⟩, ⟨.privateRow 8 20, 66940818172969475943473265⟩, ⟨.privateRow 8 21, 122692698647556327939757680⟩, ⟨.privateRow 8 22, 233345270396880209522594640⟩, ⟨.privateRow 8 23, 403681083154651424892585816⟩, ⟨.privateRow 8 25, 1721041810930596930326350800⟩, ⟨.privateRow 8 27, 6551804682243809740095664320⟩, ⟨.privateRow 9 16, 4152193536059281870597440⟩, ⟨.privateRow 9 17, 12221622577615040887385088⟩, ⟨.privateRow 9 18, 26258118903675389882191040⟩, ⟨.privateRow 9 19, 48754385871211542067345800⟩, ⟨.privateRow 9 20, 97387317873241183196323200⟩, ⟨.privateRow 9 21, 159903049963116880559979840⟩, ⟨.privateRow 9 22, 256737783873598153435685376⟩, ⟨.privateRow 9 24, 973997746803367627797456000⟩, ⟨.privateRow 9 26, 2159083563925588644437533440⟩, ⟨.privateRow 10 14, 1664385138058127090025420⟩, ⟨.privateRow 10 15, 5225913685847807508956400⟩, ⟨.privateRow 10 16, 11202718041232108861349880⟩, ⟨.privateRow 10 17, 20526326732096037563430720⟩, ⟨.privateRow 10 18, 41107696980545667411109170⟩, ⟨.privateRow 10 19, 69867739637686767499557120⟩, ⟨.privateRow 10 20, 105847046992026667788060600⟩, ⟨.privateRow 10 22, 150344007618146497731215640⟩, ⟨.privateRow 10 23, 540451032648815806364246400⟩, ⟨.privateRow 11 12, 664043639787434716286400⟩, ⟨.privateRow 11 13, 2330555363882071153027200⟩, ⟨.privateRow 11 14, 5253478232127488777232000⟩, ⟨.privateRow 11 15, 9741959232798882120791760⟩, ⟨.privateRow 11 16, 19421294699017259608560000⟩, ⟨.privateRow 11 17, 34048700431001585442313200⟩, ⟨.privateRow 11 18, 54664433064933623743125600⟩, ⟨.privateRow 11 20, 206189940525170627735629920⟩, ⟨.privateRow 11 22, 254518048795386393012996000⟩, ⟨.privateRow 11 23, 339452523102578404472553600⟩, ⟨.privateRow 12 10, 271869814861024408193880⟩, ⟨.privateRow 12 11, 1089635245287563329906320⟩, ⟨.privateRow 12 12, 2678057815460915691023220⟩, ⟨.privateRow 12 13, 5208077802960954923601600⟩, ⟨.privateRow 12 14, 10492493184677638912521744⟩, ⟨.privateRow 12 15, 18594898791926423153787600⟩, ⟨.privateRow 12 16, 30773140538831108141904180⟩, ⟨.privateRow 12 17, 47282925533046203775574800⟩, ⟨.privateRow 12 18, 19403656992606927607486920⟩, ⟨.privateRow 12 19, 107287116176311145529607152⟩, ⟨.privateRow 12 20, 109839609376248619019732580⟩, ⟨.privateRow 12 21, 91099744491747388463866800⟩, ⟨.privateRow 13 8, 118588803549917634181248⟩, ⟨.privateRow 13 9, 538134066529038003847680⟩, ⟨.privateRow 13 10, 1481018542071369549050880⟩, ⟨.privateRow 13 11, 3121675858152243605653440⟩, ⟨.privateRow 13 12, 6582629844107727501611520⟩, ⟨.privateRow 13 13, 11960029628607869635514688⟩, ⟨.privateRow 13 14, 20160096603485997810812160⟩, ⟨.privateRow 13 15, 31992817663577044103749920⟩, ⟨.privateRow 13 16, 47572546298018429090145600⟩, ⟨.privateRow 13 17, 34242517025038716869835360⟩, ⟨.privateRow 13 18, 69541869564066405597227136⟩, ⟨.privateRow 13 19, 115924915352527940266367760⟩, ⟨.privateRow 13 20, 101864294343392485478333760⟩, ⟨.privateRow 14 6, 53136067767081660536175⟩, ⟨.privateRow 14 7, 289060208652924233316792⟩, ⟨.privateRow 14 8, 886613245027876850089320⟩, ⟨.privateRow 14 9, 2079663944607011452369680⟩, ⟨.privateRow 14 10, 4739737244823684119826810⟩, ⟨.privateRow 14 11, 9112352566892985857767320⟩, ⟨.privateRow 14 12, 15813293767483502175565680⟩, ⟨.privateRow 14 13, 25571437412531565346031240⟩, ⟨.privateRow 14 14, 39001873741037938833552450⟩, ⟨.privateRow 14 15, 55893070597510811837137680⟩, ⟨.privateRow 14 17, 161074550386420662482939448⟩, ⟨.privateRow 14 18, 47524899010877837183554920⟩, ⟨.privateRow 14 19, 116332564364730782133865800⟩, ⟨.privateRow 15 4, 30006250033175525949840⟩, ⟨.privateRow 15 5, 170035416854661313715760⟩, ⟨.privateRow 15 6, 589456111762825887547968⟩, ⟨.privateRow 15 7, 1530318751691951823441840⟩, ⟨.privateRow 15 8, 3871575645306134527681920⟩, ⟨.privateRow 15 9, 8147530390952521282213500⟩, ⟨.privateRow 15 10, 15024947743884617902883520⟩, ⟨.privateRow 15 11, 25233255861231738955418784⟩, ⟨.privateRow 15 12, 39788287543990747409487840⟩, ⟨.privateRow 15 13, 59639922461772455785802820⟩, ⟨.privateRow 15 14, 85163453070348937983922080⟩, ⟨.privateRow 15 16, 228527600252664805633981440⟩, ⟨.privateRow 15 18, 42395497269095554219796160⟩, ⟨.privateRow 15 20, 1776530035297501405702260480⟩, ⟨.privateRow 16 2, 23616030118702960238300⟩, ⟨.privateRow 16 3, 100020833443918419832800⟩, ⟨.privateRow 16 4, 425088542136653284289400⟩, ⟨.privateRow 16 5, 1275265626409959852868200⟩, ⟨.privateRow 16 6, 3582889140866077681867800⟩, ⟨.privateRow 16 7, 8403673486855376466336600⟩, ⟨.privateRow 16 8, 16932693595110022490861100⟩, ⟨.privateRow 16 9, 30258575317545411054418200⟩, ⟨.privateRow 16 10, 49565324013133772948144040⟩, ⟨.privateRow 16 11, 76515937584597591172092000⟩, ⟨.privateRow 16 13, 298047794972384902756053600⟩, ⟨.privateRow 16 15, 422282957758551372613089960⟩, ⟨.privateRow 16 16, 179812453323804339254416200⟩, ⟨.privateRow 17 1, 75571296379849472762560⟩, ⟨.privateRow 17 2, 400083333775673679331200⟩, ⟨.privateRow 17 3, 1190247917982629196010320⟩, ⟨.privateRow 17 4, 3808793337544413427233024⟩, ⟨.privateRow 17 5, 10007798820588637321556160⟩, ⟨.privateRow 17 6, 3662301286100397526185600⟩, ⟨.privateRow 17 8, 221355197214431819309971200⟩, ⟨.privateRow 17 10, 270545241039861112489964800⟩, ⟨.privateRow 17 11, 50160447972125087546149200⟩, ⟨.privateRow 17 13, 1310406279226589857702790400⟩, ⟨.privateRow 17 15, 965801167734476261905516800⟩, ⟨.privateRow 18 0, 642356019228720518481760⟩, ⟨.privateRow 18 1, 1360283334837290509726080⟩, ⟨.privateRow 18 2, 5058553651426174083043860⟩, ⟨.privateRow 18 3, 14260303626877595510295072⟩, ⟨.privateRow 18 4, 35926054504006297569372720⟩, ⟨.privateRow 18 5, 16898904505863262870827840⟩, ⟨.privateRow 18 6, 2890602086529242333167920⟩, ⟨.privateRow 18 8, 1494441278735618286247814640⟩, ⟨.privateRow 18 12, 3888823340410674018888575040⟩, ⟨.privateRow 18 13, 2031515146412751511750414176⟩, ⟨.privateRow 18 16, 7489550006197266885238080720⟩, ⟨.privateRow 19 0, 14282975015791550352123840⟩, ⟨.privateRow 19 4, 18677736559112027383546560⟩, ⟨.privateRow 19 11, 36589241211287149453239531360⟩, ⟨.privateRow 20 1, 263622910291466900784914304⟩, ⟨.privateRow 20 4, 54921439644055604330190480⟩, ⟨.hall 18 10, 4219969891029321694945680⟩, ⟨.hall 19 10, 40080031628354264698505640⟩, ⟨.hall 13 11, 973911166209158413665⟩, ⟨.hall 16 13, 67031505922064625221280⟩, ⟨.hall 12 14, 307500320386065302496⟩, ⟨.hall 9 15, 194584852356922347012⟩, ⟨.hall 15 15, 41192790615719033431140⟩, ⟨.hall 19 15, 219507263897379236606688800940⟩, ⟨.hall 10 18, 1550246662947487869936⟩, ⟨.hall 6 22, 20164106313356194117500⟩, ⟨.hall 5 25, 522899534632834927110400⟩, ⟨.hall 4 30, 44175859500454640250375283200⟩, ⟨.hall 3 31, 65731207471892522190363562830⟩]
  caps := #[0, 3340706438997381977020555200, 178223629842791700713900640, 0, 6627897372014326545096960, 2277281430150696608839200, 1117979918938690990954200, 0, 760443107509164934901189, 133957569043038686701272, 0, 0, 899299445713008320137476, 87543153314136877500000, 322138813005027814750240, 51677430612691183580280, 17508630662827375500000, 69083459006986287335192864, 0, 330498094538732150506256352, 0, 0] }

theorem case_56_35_17_checked :
    (Witness.linear .positive case_56_35_17).check 56 35 17 = true := by
  change case_56_35_17.check 56 35 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_35_18 : Certificate := {
  objectiveScale := 19208436671510282356160000
  eta := 3083387490344044405826949803558400
  rows := #[⟨.count 2, 561481055340427839332685303734400⟩, ⟨.count 3, 102028270270156245202558426735680⟩, ⟨.count 4, 18198464178443840168677578979200⟩, ⟨.count 5, 3496305044536431246653652518400⟩, ⟨.count 6, 640825573471916120348738277600⟩, ⟨.count 7, 125464317258294688696630367760⟩, ⟨.count 8, 25534812123018879891290720640⟩, ⟨.count 9, 6119289295753045181048959680⟩, ⟨.count 10, 1699802582153623661402488800⟩, ⟨.count 11, 566600860717874553800829600⟩, ⟨.path 9, 112706789806891188113325120⟩, ⟨.path 10, 103876225578021375037278720⟩, ⟨.privateRow 2 33, 49010634491579718179039479902240⟩, ⟨.privateRow 3 30, 6594856284848914556539122657600⟩, ⟨.privateRow 3 31, 15376867438850253940689954348480⟩, ⟨.privateRow 4 27, 641120205919489415116714708992⟩, ⟨.privateRow 4 28, 3120034856281369386717084928200⟩, ⟨.privateRow 4 29, 5559714285708072271715260367040⟩, ⟨.privateRow 4 30, 9871414628903596788743686762800⟩, ⟨.privateRow 5 25, 506440440439874451177265959360⟩, ⟨.privateRow 5 26, 1108210846139019387282017275776⟩, ⟨.privateRow 5 27, 1965689479393164927016091436960⟩, ⟨.privateRow 5 28, 3562433660547326294577251564160⟩, ⟨.privateRow 5 29, 4621800994266417260323620435840⟩, ⟨.privateRow 6 22, 38440327144328301759425033175⟩, ⟨.privateRow 6 23, 204576636960862111216968582600⟩, ⟨.privateRow 6 24, 410643973805279582867151252600⟩, ⟨.privateRow 6 25, 692263488277420498591290258120⟩, ⟨.privateRow 6 26, 1247737724592947790841856066850⟩, ⟨.privateRow 6 27, 1712346495653405495274134944200⟩, ⟨.privateRow 6 28, 1904982918841083984197614218900⟩, ⟨.privateRow 7 20, 27035255143068066209689213840⟩, ⟨.privateRow 7 21, 77555853647678737362129388290⟩, ⟨.privateRow 7 22, 154541733810468660440971037280⟩, ⟨.privateRow 7 23, 255470884750011005066230719480⟩, ⟨.privateRow 7 24, 450934961010927642387928245456⟩, ⟨.privateRow 7 25, 622595190778318506580196585220⟩, ⟨.privateRow 7 26, 732980055685118872776922096320⟩, ⟨.privateRow 7 27, 628671985009517711169710482680⟩, ⟨.privateRow 8 17, 770062078884747689029309320⟩, ⟨.privateRow 8 18, 12337733742131718409013064540⟩, ⟨.privateRow 8 19, 31181934034840362944172322320⟩, ⟨.privateRow 8 20, 59939288553192154360205261310⟩, ⟨.privateRow 8 21, 99210461662031458478730499080⟩, ⟨.privateRow 8 22, 173464853508777294646123982040⟩, ⟨.privateRow 8 23, 240567393443595178052756231568⟩, ⟨.privateRow 8 24, 284780675107562724172219467330⟩, ⟨.privateRow 8 25, 264678148736676466565494200480⟩, ⟨.privateRow 8 26, 47755009210838193642846588120⟩, ⟨.privateRow 9 15, 604374251432399524054218240⟩, ⟨.privateRow 9 16, 5130313247954573232596602560⟩, ⟨.privateRow 9 17, 13160249324940499636280602176⟩, ⟨.privateRow 9 18, 24980802392539180327574353920⟩, ⟨.privateRow 9 19, 41050232359010011422870104520⟩, ⟨.privateRow 9 20, 72039252291272621840391192000⟩, ⟨.privateRow 9 21, 101547465370881295031193127200⟩, ⟨.privateRow 9 22, 122597316903062243454398169984⟩, ⟨.privateRow 9 23, 35223686841294534761284906800⟩, ⟨.privateRow 10 13, 305092771155778605892754400⟩, ⟨.privateRow 10 14, 2167248292245870168288173220⟩, ⟨.privateRow 10 15, 5820536114647256779953976800⟩, ⟨.privateRow 10 16, 11332017214357491076016592000⟩, ⟨.privateRow 10 17, 18691532838570772780385145360⟩, ⟨.privateRow 10 18, 32792024814046989801223013100⟩, ⟨.privateRow 10 19, 47691603876424526728492685760⟩, ⟨.privateRow 10 20, 21663039574780070440318385040⟩, ⟨.privateRow 11 11, 128772922890426034954734000⟩, ⟨.privateRow 11 12, 962825238842262353661549600⟩, ⟨.privateRow 11 13, 2742863257566074544535834200⟩, ⟨.privateRow 11 14, 5609816786281105086391684800⟩, ⟨.privateRow 11 15, 9534347210807143628048505360⟩, ⟨.privateRow 11 16, 16877837760171838981400469600⟩, ⟨.privateRow 11 17, 9529196293891526586650316000⟩, ⟨.privateRow 12 9, 49105407928882461329405232⟩, ⟨.privateRow 12 10, 449233539569171967656372040⟩, ⟨.privateRow 12 11, 1394709810997845055509734400⟩, ⟨.privateRow 12 12, 3050201300197891347961132680⟩, ⟨.privateRow 12 13, 5459971930554063882080721600⟩, ⟨.privateRow 12 14, 3467597267593392269261077152⟩, ⟨.privateRow 13 7, 18886695357262485126694320⟩, ⟨.privateRow 13 8, 216567440096609829452761536⟩, ⟨.privateRow 13 9, 771656410311010106604939360⟩, ⟨.privateRow 13 10, 1842179208692987010819107520⟩, ⟨.privateRow 13 11, 1101723895840311632390502000⟩, ⟨.privateRow 14 5, 7221383518953303136677240⟩, ⟨.privateRow 14 6, 107418079844430384158073945⟩, ⟨.privateRow 14 7, 466501375324383382629349704⟩, ⟨.privateRow 14 8, 455978787911051426630191440⟩, ⟨.privateRow 15 4, 57771068151626425093417920⟩, ⟨.privateRow 15 5, 184145279733309229985269620⟩, ⟨.privateRow 16 2, 34100977728390598145420300⟩, ⟨.privateRow 16 3, 36106917594766515683386200⟩, ⟨.hall 6 28, 414898364750842244387500585200⟩, ⟨.hall 5 29, 1645685904389947554019467341760⟩, ⟨.hall 4 30, 4379695492722856118724062511360⟩, ⟨.hall 3 31, 9748282818521924016960203143560⟩, ⟨.hall 2 32, 19206285714264249665925444904320⟩, ⟨.assumptionRow 18, 22414599158223512914008192⟩]
  caps := #[0, 0, 1330045446735184883120961017760, 89258135849856002942072709120, 9868597702877589408159298872, 0, 8442834121507057517125934625, 207426617896245778071209740, 1188506233590519297845924676, 0, 817769830119395200956702640, 5881094645049914882751984, 231989112897795274848338688, 456663990841834098092504064, 22414599158223512914008192, 1699539212695773636491149560, 0, 2212090764964088398543460736, 284920387585941004784551808, 19208436671510282356160000, 0, 0] }

theorem case_56_35_18_checked :
    (Witness.linear .conditional case_56_35_18).check 56 35 18 = true := by
  change case_56_35_18.check 56 35 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_35_19 : Certificate := {
  objectiveScale := 6811921327547874137600000
  eta := 1239262681698836164431183990067200
  rows := #[⟨.count 2, 204535715752608839175794950212480⟩, ⟨.count 3, 33382185541375813347433574586240⟩, ⟨.count 4, 5264249370764224447673076890880⟩, ⟨.count 5, 879249838666614925744519084800⟩, ⟨.count 6, 147651803715479526671743735200⟩, ⟨.count 7, 27976131230301384000961970880⟩, ⟨.count 8, 6809005484623617270075400320⟩, ⟨.count 9, 2049533423465302857213331200⟩, ⟨.count 10, 683177807821767619071110400⟩, ⟨.count 11, 170794451955441904767777600⟩, ⟨.path 8, 338105102185621673132630400⟩, ⟨.path 9, 32586535345091615384777280⟩, ⟨.privateRow 2 33, 18502880317031234399493372073920⟩, ⟨.privateRow 3 30, 2380487526167761150812012781440⟩, ⟨.privateRow 3 31, 5624090508440746482098148590400⟩, ⟨.privateRow 4 27, 217917779879628029239239225024⟩, ⟨.privateRow 4 28, 1057505161598310384385569102960⟩, ⟨.privateRow 4 29, 1996321463100518512661236934400⟩, ⟨.privateRow 4 30, 3740586371721328700509573995360⟩, ⟨.privateRow 5 25, 152363832873316884999948088320⟩, ⟨.privateRow 5 26, 362357509268665545155316956160⟩, ⟨.privateRow 5 27, 690373947397490237991992762880⟩, ⟨.privateRow 5 28, 1346406823655139623665344376320⟩, ⟨.privateRow 5 29, 1884910344373850919937829297280⟩, ⟨.privateRow 6 22, 7933046471555369305828336650⟩, ⟨.privateRow 6 23, 58125011881550211090434026800⟩, ⟨.privateRow 6 24, 129241585081782518020317041400⟩, ⟨.privateRow 6 25, 238611235678549370420903159040⟩, ⟨.privateRow 6 26, 468581695375253009143096503000⟩, ⟨.privateRow 6 27, 707482807193093421241258306800⟩, ⟨.privateRow 6 28, 867315576336228422648870625000⟩, ⟨.privateRow 7 20, 4810710396744946984292402400⟩, ⟨.privateRow 7 21, 20649049241412926286424311840⟩, ⟨.privateRow 7 22, 46870064151143626332677406240⟩, ⟨.privateRow 7 23, 86173391876051793928889033760⟩, ⟨.privateRow 7 24, 168212039841875623167688802688⟩, ⟨.privateRow 7 25, 258612689289631246151749647480⟩, ⟨.privateRow 7 26, 342374558389878842297486976960⟩, ⟨.privateRow 7 27, 344705902659070624297567141200⟩, ⟨.privateRow 8 18, 1961289623288324539749979440⟩, ⟨.privateRow 8 19, 7561449931293980772746776080⟩, ⟨.privateRow 8 20, 17415696772831466726789322150⟩, ⟨.privateRow 8 21, 32585954819270168363932272960⟩, ⟨.privateRow 8 22, 63797420953756066160923859520⟩, ⟨.privateRow 8 23, 99677919420555301514538577728⟩, ⟨.privateRow 8 24, 134098552309265397187150716900⟩, ⟨.privateRow 8 25, 148872984046960936290833345040⟩, ⟨.privateRow 8 26, 102283104127715642035263078720⟩, ⟨.privateRow 9 16, 668686157352821033212026240⟩, ⟨.privateRow 9 17, 2862515014773206323907952576⟩, ⟨.privateRow 9 18, 6796354043738028980833342720⟩, ⟨.privateRow 9 19, 12980378348613584762351097600⟩, ⟨.privateRow 9 20, 25814361452693933606329814400⟩, ⟨.privateRow 9 21, 41313280211888558519939092800⟩, ⟨.privateRow 9 22, 56963365616178984078149185152⟩, ⟨.privateRow 9 23, 65852647525619883748296116640⟩, ⟨.privateRow 9 24, 18567254643689373291643733760⟩, ⟨.privateRow 10 14, 202106768147272920641870160⟩, ⟨.privateRow 10 15, 1094637169350786753284392800⟩, ⟨.privateRow 10 16, 2809568734667019333429941520⟩, ⟨.privateRow 10 17, 5539433391754832444634920160⟩, ⟨.privateRow 10 18, 11244679730616406405148557740⟩, ⟨.privateRow 10 19, 18662953757245358993839012320⟩, ⟨.privateRow 10 20, 26709405711631856540600953680⟩, ⟨.privateRow 10 21, 18654170042573364838736669472⟩, ⟨.privateRow 11 12, 52552139063212893774700800⟩, ⟨.privateRow 11 13, 416634950982214343448669600⟩, ⟨.privateRow 11 14, 1218145554029308791856132800⟩, ⟨.privateRow 11 15, 2558811425659711445975431680⟩, ⟨.privateRow 11 16, 5363635869994635170939601600⟩, ⟨.privateRow 11 17, 9288889171122101775211177200⟩, ⟨.privateRow 11 18, 11223635414214753741882528000⟩, ⟨.privateRow 12 10, 9759682968882394558158720⟩, ⟨.privateRow 12 11, 155028810236478036635367360⟩, ⟨.privateRow 12 12, 545118959157785412717156840⟩, ⟨.privateRow 12 13, 1270089651814104346364018880⟩, ⟨.privateRow 12 14, 2831772013421226781049752608⟩, ⟨.privateRow 12 15, 5175071894249889714463661280⟩, ⟨.privateRow 12 16, 281810845726479142866833040⟩, ⟨.privateRow 13 9, 52051642500706104310179840⟩, ⟨.privateRow 13 10, 246995053597100600741093760⟩, ⟨.privateRow 13 11, 666098362626223428594332640⟩, ⟨.privateRow 13 12, 1645837446116076536853129600⟩, ⟨.privateRow 13 13, 746941069885132596851080704⟩, ⟨.privateRow 14 7, 14802185836138298413207392⟩, ⟨.privateRow 14 8, 108373146300298256239554120⟩, ⟨.privateRow 14 9, 361514923305685365091795920⟩, ⟨.privateRow 14 10, 536579236560013317478767960⟩, ⟨.privateRow 15 5, 4625683073793218254127310⟩, ⟨.privateRow 15 6, 39472495563035462435219712⟩, ⟨.privateRow 15 7, 195600312834684657603097680⟩, ⟨.privateRow 15 8, 39852038789603111112481440⟩, ⟨.privateRow 16 4, 11564207684483045635318275⟩, ⟨.privateRow 16 5, 49340619453794328044024640⟩, ⟨.hall 7 27, 31713683153926304350296837360⟩, ⟨.hall 6 28, 270880000801330860961695273600⟩, ⟨.hall 5 29, 811751871253824284980293377280⟩, ⟨.hall 4 30, 1909195478942431366947368908800⟩, ⟨.hall 3 31, 3934976077214414904421020070800⟩, ⟨.hall 2 32, 7371596198657499070129377269760⟩, ⟨.assumptionRow 19, 6399255133525023922344192⟩]
  caps := #[0, 441275976385866731293927142400, 208157986997344228569115110720, 24113221882500874960640643840, 12075751724463394313265711792, 126136492380033536868058592, 978462077677982001273127530, 0, 705724250798392920514586166, 66692840799859202908115136, 51896393327026342868500496, 142283853705291887901763936, 93963321658761362882845056, 259081155370362380320108800, 26309099408261775565574114, 6399255133525023922344192, 807036273564563219955286509, 3652404397138362323712334080, 708230555841796639616892928, 95779564779693088141655808, 6811921327547874137600000, 0] }

theorem case_56_35_19_checked :
    (Witness.linear .conditional case_56_35_19).check 56 35 19 = true := by
  change case_56_35_19.check 56 35 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_35_20 : Certificate := {
  objectiveScale := 24377818125066436800000
  eta := 4817708685576557611844308905600
  rows := #[⟨.count 2, 744075664297665327465420623040⟩, ⟨.count 3, 115508459377708523633390083200⟩, ⟨.count 4, 17204863619022050367015459840⟩, ⟨.count 5, 2611744002887597778674073600⟩, ⟨.count 6, 374928094164528196743250800⟩, ⟨.count 7, 58322147981148830604505680⟩, ⟨.count 8, 12242550013535614587534720⟩, ⟨.count 9, 3766938465703266026933760⟩, ⟨.count 10, 1177168270532270633416800⟩, ⟨.count 11, 784778847021513755611200⟩, ⟨.count 12, 470867308212908253366720⟩, ⟨.path 2, 7930902722532613784849528640⟩, ⟨.path 8, 1636440608216960616470400⟩, ⟨.privateRow 2 33, 69860071227238728708002290560⟩, ⟨.privateRow 3 30, 8440558092665387612850326400⟩, ⟨.privateRow 3 31, 20777647797972193890811008960⟩, ⟨.privateRow 4 27, 709931872451581917026041152⟩, ⟨.privateRow 4 28, 3672509950935402384289842360⟩, ⟨.privateRow 4 29, 7263119509419142902473260320⟩, ⟨.privateRow 4 30, 14230434071983460006185670160⟩, ⟨.privateRow 5 25, 482673869978098582534470720⟩, ⟨.privateRow 5 26, 1222622661351756710141800704⟩, ⟨.privateRow 5 27, 2459732340219530564212184160⟩, ⟨.privateRow 5 28, 5082925394508675538009785600⟩, ⟨.privateRow 5 29, 7556373925021148781528374400⟩, ⟨.privateRow 6 22, 23167325546447603993772300⟩, ⟨.privateRow 6 23, 177079741267211568141127200⟩, ⟨.privateRow 6 24, 420979352895998969207935800⟩, ⟨.privateRow 6 25, 830282940501311194874056080⟩, ⟨.privateRow 6 26, 1744244560522222588760480550⟩, ⟨.privateRow 6 27, 2837466018762160672631745000⟩, ⟨.privateRow 6 28, 3745030056223915434589614000⟩, ⟨.privateRow 7 20, 12903798856859297474207120⟩, ⟨.privateRow 7 21, 59788703451520284435304110⟩, ⟨.privateRow 7 22, 146619110876390812798332480⟩, ⟨.privateRow 7 23, 290930598238325507767665360⟩, ⟨.privateRow 7 24, 614712039012971581345215552⟩, ⟨.privateRow 7 25, 1028629254262273617323490120⟩, ⟨.privateRow 7 26, 1489170180813123785522626080⟩, ⟨.privateRow 7 27, 1667962421635800156894747720⟩, ⟨.privateRow 8 18, 4650468650974986930126036⟩, ⟨.privateRow 8 19, 20536499791224094223225680⟩, ⟨.privateRow 8 20, 51913938208438782343842975⟩, ⟨.privateRow 8 21, 105968500861208568726429000⟩, ⟨.privateRow 8 22, 227053959973257740915111520⟩, ⟨.privateRow 8 23, 390197274598076782714926048⟩, ⟨.privateRow 8 24, 579459446213578924479095610⟩, ⟨.privateRow 8 25, 725257731357415390102288320⟩, ⟨.privateRow 8 26, 619991638706308815136089900⟩, ⟨.privateRow 9 16, 1298452274162868213829440⟩, ⟨.privateRow 9 17, 7120560071975201475912288⟩, ⟨.privateRow 9 18, 19067219394300482358553600⟩, ⟨.privateRow 9 19, 40259154852203655662854560⟩, ⟨.privateRow 9 20, 88552950281056142633157120⟩, ⟨.privateRow 9 21, 157304560002978979458067200⟩, ⟨.privateRow 9 22, 241084061805009025723760640⟩, ⟨.privateRow 9 23, 314787875187779525938245840⟩, ⟨.privateRow 9 24, 319963055695638063871081920⟩, ⟨.privateRow 9 25, 11353133986911232331175360⟩, ⟨.privateRow 10 14, 261592949007171251870400⟩, ⟨.privateRow 10 15, 2404277013147728505827040⟩, ⟨.privateRow 10 16, 7278823806124540083293880⟩, ⟨.privateRow 10 17, 16157724483676277657195040⟩, ⟨.privateRow 10 18, 36712935437225190379686450⟩, ⟨.privateRow 10 19, 68124409484660404799592240⟩, ⟨.privateRow 10 20, 108796507492082523652899360⟩, ⟨.privateRow 10 21, 149461131415247294756153040⟩, ⟨.privateRow 10 22, 80586977853521693779325100⟩, ⟨.privateRow 11 12, 5487963965185410878400⟩, ⟨.privateRow 11 13, 749107081247808584901600⟩, ⟨.privateRow 11 14, 2824555271717927608005600⟩, ⟨.privateRow 11 15, 6877516441170356912810880⟩, ⟨.privateRow 11 16, 16389194608252320098244000⟩, ⟨.privateRow 11 17, 31984196986848398687495100⟩, ⟨.privateRow 11 18, 53879654217912109987514400⟩, ⟨.privateRow 11 19, 66016547858537035926566400⟩, ⟨.privateRow 12 11, 156955769404302751122240⟩, ⟨.privateRow 12 12, 1069261179066812492020260⟩, ⟨.privateRow 12 13, 3053503150229162612741760⟩, ⟨.privateRow 12 14, 7922342460682181362895064⟩, ⟨.privateRow 12 15, 16493435434902147430428720⟩, ⟨.privateRow 12 16, 29551828458153877359734250⟩, ⟨.privateRow 12 17, 8509244926990413435841440⟩, ⟨.privateRow 13 9, 22422252772043250160320⟩, ⟨.privateRow 13 10, 330009566439816040821120⟩, ⟨.privateRow 13 11, 1355923452353837655528240⟩, ⟨.privateRow 13 12, 4085606239948365551939520⟩, ⟨.privateRow 13 13, 9401650587317734792222176⟩, ⟨.privateRow 13 14, 8783709909996350257248320⟩, ⟨.privateRow 14 8, 78945014968235609939460⟩, ⟨.privateRow 14 9, 510106250563983941147280⟩, ⟨.privateRow 14 10, 2160866755861320861804450⟩, ⟨.privateRow 14 11, 5356115630921831382046440⟩, ⟨.privateRow 15 6, 11335694456977420914384⟩, ⟨.privateRow 15 7, 145744643018281126042080⟩, ⟨.privateRow 15 8, 994053206227250757107520⟩, ⟨.privateRow 15 9, 1473640279407064718869920⟩, ⟨.privateRow 16 5, 28339236142443552285960⟩, ⟨.privateRow 16 6, 364361607545702815105200⟩, ⟨.privateRow 16 7, 392389423510756877805600⟩, ⟨.privateRow 17 4, 90685555655819367315072⟩, ⟨.privateRow 17 5, 97163095345520750694720⟩, ⟨.hall 7 27, 345809529028167446769426900⟩, ⟨.hall 6 28, 1448174055480441306022605600⟩, ⟨.hall 5 29, 3729896904123850577668911360⟩, ⟨.hall 4 30, 8078020643877461993774298240⟩, ⟨.hall 3 31, 15752336070541106094598580040⟩, ⟨.hall 2 32, 28399377154126207039102131840⟩, ⟨.assumptionRow 20, 16264218139465621124800⟩]
  caps := #[0, 1304711845934304799214213760, 2302527211233876615690240, 82789471935317224748784960, 0, 0, 0, 2340547312947316792875732, 134614632633944204202692, 0, 11119144191847432602400, 68224873898189814200220, 0, 460863685395817209857472, 81836991432726411408428, 1827820217768524408916256, 24414836293330426574400, 676592277736941930927552, 11326091101439732705348800, 2291329812914925110328000, 325025235611464494075200, 24377818125066436800000] }

theorem case_56_35_20_checked :
    (Witness.linear .conditional case_56_35_20).check 56 35 20 = true := by
  change case_56_35_20.check 56 35 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_35_21 : Certificate := {
  objectiveScale := 10648232565258288000000
  eta := 5124343948247315002080379910400
  rows := #[⟨.count 2, 474555329720560821900103896960⟩, ⟨.count 3, 65916312329162837159284867200⟩, ⟨.count 4, 10698238550547834273775307520⟩, ⟨.count 5, 1770101226906041232576172800⟩, ⟨.count 6, 262211729180093977298414400⟩, ⟨.count 7, 36613291318585300767127680⟩, ⟨.count 8, 4129318569765259485014400⟩, ⟨.count 9, 381167867978331644770560⟩, ⟨.path 2, 90699350302050078831808325760⟩, ⟨.path 9, 287118090092871376859520⟩, ⟨.privateRow 2 33, 44014406635127900850768489600⟩, ⟨.privateRow 3 30, 5531635156057541606125290240⟩, ⟨.privateRow 3 31, 12958627535637337315872190080⟩, ⟨.privateRow 4 27, 440846050508139102620137344⟩, ⟨.privateRow 4 28, 2287298377769139983074226400⟩, ⟨.privateRow 4 29, 4527017829351095809637786880⟩, ⟨.privateRow 4 30, 8919878686502262522229105920⟩, ⟨.privateRow 5 25, 302357881941700666736054400⟩, ⟨.privateRow 5 26, 755500125524251875378234624⟩, ⟨.privateRow 5 27, 1520002165530592016433800640⟩, ⟨.privateRow 5 28, 3170399035230882560161056000⟩, ⟨.privateRow 5 29, 4783402631216076587440680960⟩, ⟨.privateRow 6 22, 18345358020884199691235850⟩, ⟨.privateRow 6 23, 111712814878470859282086000⟩, ⟨.privateRow 6 24, 258885333665560851602152800⟩, ⟨.privateRow 6 25, 507768540128801408007270720⟩, ⟨.privateRow 6 26, 1076762830801393132170473700⟩, ⟨.privateRow 6 27, 1785184710015044888750600400⟩, ⟨.privateRow 6 28, 2415393280902066470015610600⟩, ⟨.privateRow 7 19, 247759114185915569100864⟩, ⟨.privateRow 7 20, 11340332294373851511622880⟩, ⟨.privateRow 7 21, 38290826987552437432914780⟩, ⟨.privateRow 7 22, 89566886120384556924955200⟩, ⟨.privateRow 7 23, 175679564484790872979112640⟩, ⟨.privateRow 7 24, 374308963953988221451605312⟩, ⟨.privateRow 7 25, 639837912385126957202981280⟩, ⟨.privateRow 7 26, 955707842313448389698332800⟩, ⟨.privateRow 7 27, 1114709547908131797979637280⟩, ⟨.privateRow 8 17, 494266919714326514115360⟩, ⟨.privateRow 8 18, 4497516142235995122428184⟩, ⟨.privateRow 8 19, 13668809154547039499006000⟩, ⟨.privateRow 8 20, 31559177444133030043281930⟩, ⟨.privateRow 8 21, 63075341153164338633594960⟩, ⟨.privateRow 8 22, 136020900721003693341786840⟩, ⟨.privateRow 8 23, 239121956177489901344708880⟩, ⟨.privateRow 8 24, 367733024131637045721719880⟩, ⟨.privateRow 8 25, 482843514428523883393558800⟩, ⟨.privateRow 8 26, 445587884665752875595428880⟩, ⟨.privateRow 9 15, 282346568872838255385600⟩, ⟨.privateRow 9 16, 1655577608390733406579200⟩, ⟨.privateRow 9 17, 5037768655113616571717568⟩, ⟨.privateRow 9 18, 11712676832074906960912640⟩, ⟨.privateRow 9 19, 23669465801821121996794080⟩, ⟨.privateRow 9 20, 52126218516941528341599360⟩, ⟨.privateRow 9 21, 94699039199949950856330240⟩, ⟨.privateRow 9 22, 150582483844106462553525120⟩, ⟨.privateRow 9 23, 206746510391080357267009440⟩, ⟨.privateRow 9 24, 226921937403100105853406720⟩, ⟨.privateRow 9 25, 80775824022408114387627840⟩, ⟨.privateRow 10 12, 1134428178506939418960⟩, ⟨.privateRow 10 13, 117282420916409736852480⟩, ⟨.privateRow 10 14, 624691783631154640040640⟩, ⟨.privateRow 10 15, 1934715693526380318153600⟩, ⟨.privateRow 10 16, 4628013197036910053589216⟩, ⟨.privateRow 10 17, 9515079371014649206494720⟩, ⟨.privateRow 10 18, 21277902130165409211723240⟩, ⟨.privateRow 10 19, 40220016640785030159807840⟩, ⟨.privateRow 10 20, 66595849933797540630434160⟩, ⟨.privateRow 10 21, 96111477910736324228896704⟩, ⟨.privateRow 10 22, 94227873363143402017655520⟩, ⟨.privateRow 11 11, 46408425484374794412000⟩, ⟨.privateRow 11 12, 247670263867039501118400⟩, ⟨.privateRow 11 13, 792896543553410839342800⟩, ⟨.privateRow 11 14, 1967529731747655425313600⟩, ⟨.privateRow 11 15, 4161082558763453788745280⟩, ⟨.privateRow 11 16, 9473048234057442602568000⟩, ⟨.privateRow 11 17, 18549447666104605326476400⟩, ⟨.privateRow 11 18, 32236323639790829416228800⟩, ⟨.privateRow 11 19, 49190868416749087641412800⟩, ⟨.privateRow 11 20, 16667431317961592830421760⟩, ⟨.privateRow 12 9, 17999593765643438780832⟩, ⟨.privateRow 12 10, 105501820601145365963280⟩, ⟨.privateRow 12 11, 354290646518321080075200⟩, ⟨.privateRow 12 12, 917185182322860520229160⟩, ⟨.privateRow 12 13, 2006906577613185553905600⟩, ⟨.privateRow 12 14, 4688364776133479230677888⟩, ⟨.privateRow 12 15, 9509785372848283489206240⟩, ⟨.privateRow 12 16, 17309388754703508389346420⟩, ⟨.privateRow 12 17, 16825838743614925462014720⟩, ⟨.privateRow 13 7, 7940997249548575932720⟩, ⟨.privateRow 13 8, 49410649552746694692480⟩, ⟨.privateRow 13 9, 175458224942406630132480⟩, ⟨.privateRow 13 10, 478903218742006425480960⟩, ⟨.privateRow 13 11, 1088798956215882522330720⟩, ⟨.privateRow 13 12, 2620047819790451356225920⟩, ⟨.privateRow 13 13, 5531169284218901423003904⟩, ⟨.privateRow 13 14, 9298613668212139877365760⟩, ⟨.privateRow 14 5, 4048351538985548514720⟩, ⟨.privateRow 14 6, 25808241061032871781340⟩, ⟨.privateRow 14 7, 98644832499947865475344⟩, ⟨.privateRow 14 8, 285119615531410773965280⟩, ⟨.privateRow 14 9, 677631765294811812925440⟩, ⟨.privateRow 14 10, 1686138415987480956380880⟩, ⟨.privateRow 14 11, 3713258441144971976297040⟩, ⟨.privateRow 14 12, 402608560552112799788904⟩, ⟨.privateRow 15 3, 3823443120153018041680⟩, ⟨.privateRow 15 4, 16193406155942194058880⟩, ⟨.privateRow 15 5, 64520602652582179453350⟩, ⟨.privateRow 15 6, 197289664999895730950688⟩, ⟨.privateRow 15 7, 491585544019673748216000⟩, ⟨.privateRow 15 8, 1275853558094137866523680⟩, ⟨.privateRow 15 9, 286758234011476353126000⟩, ⟨.privateRow 16 2, 9558607800382545104200⟩, ⟨.privateRow 16 3, 50604394237319356434000⟩, ⟨.privateRow 16 4, 161301506631455448633375⟩, ⟨.privateRow 16 5, 424402186336985002626480⟩, ⟨.privateRow 16 6, 73737831602951062232400⟩, ⟨.privateRow 17 1, 61175089922448288666880⟩, ⟨.privateRow 17 2, 161934061559421940588800⟩, ⟨.hall 7 27, 280415141875142496194852880⟩, ⟨.hall 6 28, 1006343413510895565873768000⟩, ⟨.hall 5 29, 2468690166275439465007608960⟩, ⟨.hall 4 30, 5213100409611348363700631040⟩, ⟨.hall 3 31, 10017752658491580543516715740⟩, ⟨.hall 2 32, 17904850449367915589431075200⟩, ⟨.assumptionRow 21, 1914778789460095027392⟩]
  caps := #[0, 446301444765178505947086720, 0, 1411185471030806653105308, 1399812685399356552645552, 468850192434900682249536, 518340712795537052777070, 228213969387641716506016, 0, 0, 159140899746777429936840, 72926132965038003023616, 13183596646486996730616, 206949577664305769975616, 63391044921582967047492, 0, 4126794763926381294566841, 0, 17060355699472797905098752, 4486085334609796837151232, 931534027820804589616512, 136512244558897648972608] }

theorem case_56_35_21_checked :
    (Witness.linear .conditional case_56_35_21).check 56 35 21 = true := by
  change case_56_35_21.check 56 35 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_35_22 : Certificate := {
  objectiveScale := 17944242936366848626668000000
  eta := 17162520192211031605185142282514956800
  rows := #[⟨.count 2, 958080290281323334646659797824605440⟩, ⟨.count 3, 90484927765119693445438218927386880⟩, ⟨.count 4, 14418356276095730652373876401004800⟩, ⟨.count 5, 2322830051898835250832887348121600⟩, ⟨.count 6, 332378642294734649379048025142400⟩, ⟨.count 7, 42788974640241701989026872202240⟩, ⟨.count 8, 4584532997168753784538593450240⟩, ⟨.count 9, 528984576596394667446760782720⟩, ⟨.path 2, 440073366059355392038220105283884160⟩, ⟨.path 8, 355389051921652554803312515200⟩, ⟨.path 9, 289482842977575655685336579520⟩, ⟨.privateRow 2 33, 92550259880344217025372855276720000⟩, ⟨.privateRow 3 32, 152522828282807269657814465496034560⟩, ⟨.privateRow 5 25, 370837780215428083904899559086080⟩, ⟨.privateRow 6 22, 21131831783824724475607579184700⟩, ⟨.privateRow 6 23, 149270211276863590484679203409600⟩, ⟨.privateRow 6 24, 316221347183185048367566523920200⟩, ⟨.privateRow 7 20, 12840937330032852035397449247200⟩, ⟨.privateRow 7 21, 50095574104479403333135255513560⟩, ⟨.privateRow 7 22, 124219013113762900162021889199360⟩, ⟨.privateRow 7 23, 258994277305332028036260123039600⟩, ⟨.privateRow 7 24, 371003332795881400013785674960672⟩, ⟨.privateRow 7 25, 687584438471205385310277796839120⟩, ⟨.privateRow 7 26, 1029800724489031318851981553760160⟩, ⟨.privateRow 8 17, 321264622907658882628651434960⟩, ⟨.privateRow 8 18, 4909270751134873844276743819632⟩, ⟨.privateRow 8 20, 76934194358738149446788271336840⟩, ⟨.privateRow 8 22, 377428046398858167470173787170800⟩, ⟨.privateRow 8 24, 1232737942941829435595697729455940⟩, ⟨.privateRow 9 15, 200818218893075753382566593440⟩, ⟨.privateRow 9 16, 1688476022267279948617943508480⟩, ⟨.privateRow 9 17, 3250316342864513901089541253824⟩, ⟨.privateRow 9 18, 11173982846375694765449477768320⟩, ⟨.privateRow 9 19, 49305770743588952961600161289360⟩, ⟨.privateRow 9 20, 32100127560762171645221690037120⟩, ⟨.privateRow 9 21, 241079822778468014182681164124800⟩, ⟨.privateRow 9 22, 153875735725484582152846636573440⟩, ⟨.privateRow 9 23, 585292045971877566492760430480640⟩, ⟨.privateRow 9 26, 1855971775020483823774040581772160⟩, ⟨.privateRow 10 13, 84773169326345299270314228000⟩, ⟨.privateRow 10 14, 587760640662660741607511980800⟩, ⟨.privateRow 10 15, 1655080531320537861026607600480⟩, ⟨.privateRow 10 16, 3918894071618290494668086131984⟩, ⟨.privateRow 10 17, 10329893259646262533752023062560⟩, ⟨.privateRow 10 18, 42120396911487925395448327324080⟩, ⟨.privateRow 10 19, 38552899737180097072727017997760⟩, ⟨.privateRow 10 20, 160884781365386811496516216944480⟩, ⟨.privateRow 10 21, 167079778517971255713059393222112⟩, ⟨.privateRow 10 22, 321468335402434009362958583998800⟩, ⟨.privateRow 10 23, 283006748479071147084017018755200⟩, ⟨.privateRow 11 11, 31487177178356825443259570400⟩, ⟨.privateRow 11 12, 209620927788781103650231545600⟩, ⟨.privateRow 11 14, 3042025629875961069683507256000⟩, ⟨.privateRow 11 15, 2897392794539343519424303378080⟩, ⟨.privateRow 11 16, 10223472961829311081294299302400⟩, ⟨.privateRow 11 17, 34173605885801178232214034656400⟩, ⟨.privateRow 11 19, 169288422707224990417999984833600⟩, ⟨.privateRow 11 20, 85487113545108265499805310734720⟩, ⟨.privateRow 12 9, 11755212813253214832150239616⟩, ⟨.privateRow 12 10, 85015378381563428696800840080⟩, ⟨.privateRow 12 11, 162764485106582974599003317760⟩, ⟨.privateRow 12 12, 385717920434871111679929737400⟩, ⟨.privateRow 12 13, 3033646397602051236796953882720⟩, ⟨.privateRow 12 14, 3764606903444342049996114237024⟩, ⟨.privateRow 12 15, 11324188343433930288304730830080⟩, ⟨.privateRow 12 16, 32934800149131780493013429149140⟩, ⟨.privateRow 12 17, 15573557832415285864236183519840⟩, ⟨.privateRow 12 18, 61340169861156931646013969096240⟩, ⟨.privateRow 12 19, 242927350392284311113800776784448⟩, ⟨.privateRow 13 7, 7347008008283259270093899760⟩, ⟨.privateRow 13 8, 39184042710844049440500798720⟩, ⟨.privateRow 13 9, 113353837842084571595734453440⟩, ⟨.privateRow 13 10, 221540549172849048759754515840⟩, ⟨.privateRow 13 11, 499596544563261630366385183680⟩, ⟨.privateRow 13 12, 3927309735336869500741102780800⟩, ⟨.privateRow 13 14, 22341435018966248855992205403520⟩, ⟨.privateRow 13 15, 29057416672760290413221373550800⟩, ⟨.privateRow 13 16, 25953830575546919318697421895040⟩, ⟨.privateRow 13 17, 50743335310543044025448534342400⟩, ⟨.privateRow 13 18, 169286819723659546797795600710016⟩, ⟨.privateRow 14 5, 5618300241628374735954158640⟩, ⟨.privateRow 14 6, 17908332020190444470853880665⟩, ⟨.privateRow 14 7, 70041476345633738374895177712⟩, ⟨.privateRow 14 8, 170555543049432804484322673000⟩, ⟨.privateRow 14 9, 323268352364463407884131589440⟩, ⟨.privateRow 14 10, 795925867564019754260172474000⟩, ⟨.privateRow 14 11, 5478864244722506890234569066480⟩, ⟨.privateRow 14 12, 544413293413789511913957972216⟩, ⟨.privateRow 14 13, 24843499412898269929640850155120⟩, ⟨.privateRow 14 14, 35912175144488571312218982026880⟩, ⟨.privateRow 14 15, 32405553179392232852021307870000⟩, ⟨.privateRow 14 16, 41865700633867439074085072132400⟩, ⟨.privateRow 15 4, 11236600483256749471908317280⟩, ⟨.privateRow 15 5, 47755552053841185255610348440⟩, ⟨.privateRow 15 6, 140082952691267476749790355424⟩, ⟨.privateRow 15 7, 300177755767001735892407904480⟩, ⟨.privateRow 15 8, 617148672695793778687887579840⟩, ⟨.privateRow 15 9, 1416748044263955162583107003720⟩, ⟨.privateRow 15 10, 8891215509660613400317272145920⟩, ⟨.privateRow 15 11, 2750719798301252270723156070144⟩, ⟨.privateRow 15 12, 33152965470266636164117050783680⟩, ⟨.privateRow 15 13, 57497684672824787047754859521760⟩, ⟨.privateRow 15 15, 200223111244404809381688987559440⟩, ⟨.privateRow 15 19, 393887793340082095988274153933120⟩, ⟨.privateRow 16 3, 28091501208141873679770793200⟩, ⟨.privateRow 16 4, 119388880134602963139025871100⟩, ⟨.privateRow 16 5, 286533312323047111533662090640⟩, ⟨.privateRow 16 6, 682222172197731217937290692000⟩, ⟨.privateRow 16 7, 1322461441490986668616901956800⟩, ⟨.privateRow 16 8, 2944925709986873090762638153800⟩, ⟨.privateRow 16 9, 16757857357075179553332358634400⟩, ⟨.privateRow 16 10, 8739266025852936901776693764520⟩, ⟨.privateRow 16 11, 50302514830046048469242900356800⟩, ⟨.privateRow 16 12, 100406048193201091999920757595100⟩, ⟨.privateRow 16 13, 47550885402181865890229161232400⟩, ⟨.privateRow 17 1, 84898759206828773787751730560⟩, ⟨.privateRow 17 2, 89892803866053995775266538240⟩, ⟨.privateRow 17 3, 382044416430729482044882787520⟩, ⟨.privateRow 17 4, 916906599433750756907718690048⟩, ⟨.privateRow 17 5, 1964799855929465907659397192960⟩, ⟨.privateRow 17 6, 3644115972108496597966574280960⟩, ⟨.privateRow 17 7, 7640888328614589640897655750400⟩, ⟨.privateRow 17 8, 38760142612426736542008108261120⟩, ⟨.privateRow 17 10, 163005617677111245672483322675200⟩, ⟨.privateRow 17 11, 194078563546810576878800456060160⟩, ⟨.privateRow 17 12, 218966028388583811709152820504320⟩, ⟨.privateRow 17 14, 265902913835787719503238420113920⟩, ⟨.privateRow 17 16, 156383514458978601317038687691520⟩, ⟨.privateRow 17 17, 167335454396659513135658660933760⟩, ⟨.privateRow 18 0, 360819726629022288597944854880⟩, ⟨.privateRow 18 1, 382044416430729482044882787520⟩, ⟨.privateRow 18 2, 1217766577372950224018063885220⟩, ⟨.privateRow 18 3, 3463869375638613970540270606848⟩, ⟨.privateRow 18 4, 6958666156416858422960365058400⟩, ⟨.privateRow 18 5, 12989510158644802389526014775680⟩, ⟨.privateRow 18 7, 165911470662690430520764097816640⟩, ⟨.privateRow 18 9, 412056127810343453578853024272960⟩, ⟨.privateRow 18 10, 650287352317155419625646114707480⟩, ⟨.privateRow 18 15, 6310737018741599827578055511851200⟩, ⟨.privateRow 19 0, 6876799495753130676807890175360⟩, ⟨.privateRow 19 1, 4871066309491800896072255540880⟩, ⟨.privateRow 19 2, 18185314222102723345336420685952⟩, ⟨.privateRow 19 3, 36185064013367663799393898303680⟩, ⟨.privateRow 19 4, 62949164614970965426164533143680⟩, ⟨.privateRow 19 5, 16236887698306002986907518469600⟩, ⟨.privateRow 19 8, 779370609518688143371560886540800⟩, ⟨.privateRow 19 10, 439787701085545452331095071690880⟩, ⟨.privateRow 19 12, 14052052089621947224989242784330624⟩, ⟨.privateRow 19 15, 27433845455057822646678943206236160⟩, ⟨.privateRow 20 0, 138825389820516325538059282915080⟩, ⟨.privateRow 20 6, 2776507796410326510761185658301600⟩, ⟨.privateRow 20 8, 2406306756888949642659694237194720⟩, ⟨.privateRow 20 11, 30134364617040077063461401678100032⟩, ⟨.privateRow 20 12, 40907214867112143925214802032310240⟩, ⟨.hall 19 4, 53089269953340309106862231268624⟩, ⟨.hall 15 9, 11714269734569283356341666800⟩, ⟨.hall 13 10, 1929287495561013481282749360⟩, ⟨.hall 19 10, 57277608387485756690527955888040⟩, ⟨.hall 10 12, 299378442272172765610247568⟩, ⟨.hall 15 13, 21610742596088090541367531260⟩, ⟨.hall 16 13, 126953872126620116840508005760⟩, ⟨.hall 11 15, 116727632465168422101003600⟩, ⟨.hall 17 16, 9338863512751165116652690361600⟩, ⟨.hall 18 16, 165043187898075136243389364208640⟩, ⟨.hall 12 18, 12582818363331875890052819712⟩, ⟨.hall 14 18, 183314294550534233928553407696⟩, ⟨.hall 6 21, 4146565069051876747878742140⟩, ⟨.hall 8 26, 208511352611971468422718250255360⟩, ⟨.hall 4 30, 43430217707200531550632012240957440⟩, ⟨.hall 3 31, 65335612409213525419017163569823440⟩]
  caps := #[0, 6577711412395363514948635909009920, 0, 0, 15732179057378650602212269752960, 754528034714510871852312475200, 1932814283381825516795965994580, 558169782420759816737008610460, 502641939479798490670868631204, 0, 0, 828848332608635041516318103712, 251807590390935669955109835480, 15558369899893960807257670080, 3622251381334454758772200003829, 0, 20216472814823935961914769560680, 0, 30105935719544821180893112108416, 0, 0, 1381706706100247344253436000000] }

theorem case_56_35_22_checked :
    (Witness.linear .conditional case_56_35_22).check 56 35 22 = true := by
  change case_56_35_22.check 56 35 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_36_1_checked :
    (Witness.rising).check 56 36 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_36_2_checked :
    (Witness.rising).check 56 36 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_36_3_checked :
    (Witness.rising).check 56 36 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_36_4_checked :
    (Witness.rising).check 56 36 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_36_5_checked :
    (Witness.rising).check 56 36 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_36_6_checked :
    (Witness.rising).check 56 36 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_36_7_checked :
    (Witness.rising).check 56 36 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_36_8_checked :
    (Witness.rising).check 56 36 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_36_9_checked :
    (Witness.rising).check 56 36 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_36_10_checked :
    (Witness.rising).check 56 36 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_36_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_36_11_checked :
    (Witness.linear .positive case_56_36_11).check 56 36 11 = true := by
  change case_56_36_11.check 56 36 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_36_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_36_12_checked :
    (Witness.linear .positive case_56_36_12).check 56 36 12 = true := by
  change case_56_36_12.check 56 36 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_36_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_36_13_checked :
    (Witness.linear .positive case_56_36_13).check 56 36 13 = true := by
  change case_56_36_13.check 56 36 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_36_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_36_14_checked :
    (Witness.linear .positive case_56_36_14).check 56 36 14 = true := by
  change case_56_36_14.check 56 36 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_36_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_56_36_15_checked :
    (Witness.linear .positive case_56_36_15).check 56 36 15 = true := by
  change case_56_36_15.check 56 36 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_36_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_56_36_16_checked :
    (Witness.linear .positive case_56_36_16).check 56 36 16 = true := by
  change case_56_36_16.check 56 36 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_36_17 : Certificate := {
  objectiveScale := 7767944285749648000000
  eta := 6694539232556391817174399425600
  rows := #[⟨.count 2, 925950350922960830317625174400⟩, ⟨.count 3, 126212837063121291132903052800⟩, ⟨.count 4, 16895594019827178406316966400⟩, ⟨.count 5, 2219838160945874197258530000⟩, ⟨.count 6, 295978421459449892967804000⟩, ⟨.count 7, 47738455074104821446420000⟩, ⟨.count 8, 11163454109636819784393600⟩, ⟨.count 9, 3525301297780048352966400⟩, ⟨.count 10, 1201807260606834665784000⟩, ⟨.count 11, 440662662222506044120800⟩, ⟨.path 7, 6029494682238718001110800⟩, ⟨.path 8, 239254556666274804480000⟩, ⟨.privateRow 2 34, 84531437168818889431604822400⟩, ⟨.privateRow 5 25, 213186300802359531202155600⟩, ⟨.privateRow 5 26, 563154641690856543662934600⟩, ⟨.privateRow 5 27, 1157562058636893710432792160⟩, ⟨.privateRow 6 22, 17928442016719366276544400⟩, ⟨.privateRow 6 23, 119187009501681704211228600⟩, ⟨.privateRow 6 24, 257833122595474707069188400⟩, ⟨.privateRow 6 28, 7833562221293440500547879200⟩, ⟨.privateRow 7 20, 13666837709786580311232240⟩, ⟨.privateRow 7 21, 50102645230155726889480800⟩, ⟨.privateRow 7 22, 104018683716826255587360150⟩, ⟨.privateRow 7 23, 153795765673432390072078800⟩, ⟨.privateRow 7 24, 181360664086289650237875600⟩, ⟨.privateRow 7 25, 317365249332648852975800160⟩, ⟨.privateRow 7 26, 533715927728491903770975600⟩, ⟨.privateRow 8 18, 7090662837580324528125600⟩, ⟨.privateRow 8 19, 20791933279198576848433080⟩, ⟨.privateRow 8 20, 42621871940521279045239600⟩, ⟨.privateRow 8 21, 72782783043750581620618800⟩, ⟨.privateRow 8 22, 111267322211182776140502000⟩, ⟨.privateRow 8 23, 172862169886284176529831600⟩, ⟨.privateRow 8 24, 268554515113802600155352880⟩, ⟨.privateRow 8 25, 421291866028975049264656500⟩, ⟨.privateRow 8 27, 1394366828937564750109241400⟩, ⟨.privateRow 9 16, 3288649127327221032975600⟩, ⟨.privateRow 9 17, 9191599974641161425348000⟩, ⟨.privateRow 9 18, 18610653101197171930035120⟩, ⟨.privateRow 9 19, 32407746652586030923797600⟩, ⟨.privateRow 9 20, 51447365814477580651103400⟩, ⟨.privateRow 9 21, 89993108129440678788225600⟩, ⟨.privateRow 9 22, 126510986156213170407495600⟩, ⟨.privateRow 9 23, 187634161574343073586636640⟩, ⟨.privateRow 9 24, 272660022250175614799745000⟩, ⟨.privateRow 9 26, 670615128125617114811170800⟩, ⟨.privateRow 10 14, 1497636740140824737361600⟩, ⟨.privateRow 10 15, 4409964975726746093057400⟩, ⟨.privateRow 10 16, 8977136052714689245932000⟩, ⟨.privateRow 10 17, 15667560654111101259604080⟩, ⟨.privateRow 10 18, 24993139882619913512508000⟩, ⟨.privateRow 10 19, 44476883702957939589556200⟩, ⟨.privateRow 10 20, 68216869268730805791168000⟩, ⟨.privateRow 10 21, 93614108894269049160874800⟩, ⟨.privateRow 10 23, 204908137933465310516172000⟩, ⟨.privateRow 11 12, 701054235353986888374000⟩, ⟨.privateRow 11 13, 2301923137623860244463200⟩, ⟨.privateRow 11 14, 4880672819464423003822800⟩, ⟨.privateRow 11 15, 8605668353981667621962400⟩, ⟨.privateRow 11 16, 13720632891928029101034000⟩, ⟨.privateRow 11 17, 24200837318219852140250400⟩, ⟨.privateRow 11 18, 37766793164569779372262200⟩, ⟨.privateRow 11 19, 54493374930944188988548800⟩, ⟨.privateRow 11 21, 168124823710492124178743040⟩, ⟨.privateRow 12 10, 349265961909689975710560⟩, ⟨.privateRow 12 11, 1314993341235414861820800⟩, ⟨.privateRow 12 13, 11567394883340783658171000⟩, ⟨.privateRow 12 14, 5964524923011697970928000⟩, ⟨.privateRow 12 15, 15824685825590439273315840⟩, ⟨.privateRow 12 17, 65903549261277015042955200⟩, ⟨.privateRow 12 18, 71883971105725311356023200⟩, ⟨.privateRow 12 20, 98894493906335300879465760⟩, ⟨.privateRow 13 8, 188199678657528623009925⟩, ⟨.privateRow 13 10, 2974472970001915797815400⟩, ⟨.privateRow 13 11, 621447344159944421196000⟩, ⟨.privateRow 13 12, 2564411881544861562314100⟩, ⟨.privateRow 13 13, 31407229743858612599155200⟩, ⟨.privateRow 13 14, 7072635728671222008138840⟩, ⟨.privateRow 13 16, 62041630652076996795174300⟩, ⟨.privateRow 13 18, 166117583028378597910093800⟩, ⟨.privateRow 14 6, 112325776644952521050400⟩, ⟨.privateRow 14 7, 221642827129772385286950⟩, ⟨.privateRow 14 8, 863838710864753911887600⟩, ⟨.privateRow 14 9, 4374401291484298944784200⟩, ⟨.privateRow 14 10, 1049196814815490581240000⟩, ⟨.privateRow 14 11, 4580618427348629295930300⟩, ⟨.privateRow 14 12, 49796788461715574786707200⟩, ⟨.privateRow 14 13, 15617294588528577301757400⟩, ⟨.privateRow 14 15, 83508197483201934087344700⟩, ⟨.privateRow 14 16, 39184503328173386093367600⟩, ⟨.privateRow 14 20, 832376795711153400991483200⟩, ⟨.privateRow 15 4, 70723637146821957698400⟩, ⟨.privateRow 15 5, 280814441612381302626000⟩, ⟨.privateRow 15 6, 676294780216484970490950⟩, ⟨.privateRow 15 7, 2333880025845124604047200⟩, ⟨.privateRow 15 8, 8752050096919217265177000⟩, ⟨.privateRow 15 9, 2276757088149614561290800⟩, ⟨.privateRow 15 10, 9176391919800149011367400⟩, ⟨.privateRow 15 11, 57720132044144920476126000⟩, ⟨.privateRow 15 13, 196187369445284110655361600⟩, ⟨.privateRow 15 15, 115299735302790311607734400⟩, ⟨.privateRow 15 19, 573073631800698323230135200⟩, ⟨.privateRow 15 21, 2539367553575215802139901200⟩, ⟨.privateRow 16 2, 50251005341162969943600⟩, ⟨.privateRow 16 3, 318256367160698809642800⟩, ⟨.privateRow 16 4, 898606213159620168403200⟩, ⟨.privateRow 16 5, 2088557409492085938280875⟩, ⟨.privateRow 16 6, 6046870976053277383213200⟩, ⟨.privateRow 16 7, 2045933788890206633418000⟩, ⟨.privateRow 16 8, 50896537486699448095952400⟩, ⟨.privateRow 16 10, 130629772520959556867022000⟩, ⟨.privateRow 16 11, 34658118383800100370100920⟩, ⟨.privateRow 16 15, 1203486452418182548664248200⟩, ⟨.privateRow 17 1, 603012064093955639323200⟩, ⟨.privateRow 17 2, 1273025468642795238571200⟩, ⟨.privateRow 17 3, 3369773299348575631512000⟩, ⟨.privateRow 17 4, 7160768261115723216963000⟩, ⟨.privateRow 17 5, 22659853341841755246567360⟩, ⟨.privateRow 17 6, 7092570468152716329182400⟩, ⟨.privateRow 17 8, 357401900321464763228864400⟩, ⟨.privateRow 17 9, 193384141645646440332043200⟩, ⟨.privateRow 17 10, 217305447497325147224103840⟩, ⟨.privateRow 17 11, 43282865933855038111420800⟩, ⟨.privateRow 17 17, 8123175515409676417322827200⟩, ⟨.privateRow 18 1, 15629923809447652651346400⟩, ⟨.privateRow 18 2, 12730254686427952385712000⟩, ⟨.privateRow 18 4, 190444610108962167690251520⟩, ⟨.privateRow 18 9, 601631836480585029748749120⟩, ⟨.privateRow 18 13, 8400482896662365313458253600⟩, ⟨.privateRow 18 18, 62825079902990587818727291200⟩, ⟨.privateRow 19 6, 4690780595581539755325229200⟩, ⟨.privateRow 19 9, 2099218997791969348403908800⟩, ⟨.privateRow 19 12, 25223090122954023459430471200⟩, ⟨.privateRow 19 16, 150072516909158880891823768800⟩, ⟨.hall 18 4, 8401968093042448574569920⟩, ⟨.hall 17 5, 470870531530156718360400⟩, ⟨.hall 12 9, 653605487710564088700⟩, ⟨.hall 18 9, 2207319335314553002823280⟩, ⟨.hall 17 10, 335709513537932568434400⟩, ⟨.hall 15 12, 12541637467500337876680⟩, ⟨.hall 16 12, 50175211969607671346400⟩, ⟨.hall 10 13, 62386375786169070636⟩, ⟨.hall 11 17, 806399532352259517672⟩, ⟨.hall 12 21, 125793030498299924760000⟩, ⟨.hall 8 22, 6646082833647288163440⟩, ⟨.hall 9 26, 41471252766940291041146400⟩, ⟨.hall 5 27, 683988209400391105310100⟩, ⟨.hall 7 27, 6589317789046389640042800⟩, ⟨.hall 3 32, 59441146748161921202743483200⟩, ⟨.hall 2 33, 76912379738991759928756190400⟩]
  caps := #[0, 0, 43176829688693014222490400, 0, 0, 5491226325523901653291440, 540230175367767713612000, 365366745441631611330800, 596914154002233672650220, 0, 101669580604775948162720, 229081834904232006773160, 121414656378333734192392, 38839721428748240000000, 969867568984640023748050, 1310463646746930979453150, 666301281939966884411200, 35874894628825324177064960, 357551908878149864539140480, 0, 0] }

theorem case_56_36_17_checked :
    (Witness.linear .positive case_56_36_17).check 56 36 17 = true := by
  change case_56_36_17.check 56 36 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_36_18 : Certificate := {
  objectiveScale := 4772344539427264800000
  eta := 1987097810502384813675153872160
  rows := #[⟨.count 2, 307184202589740647524661468160⟩, ⟨.count 3, 48053669118570539890553767680⟩, ⟨.count 4, 7621486278563826695120814720⟩, ⟨.count 5, 1201176617776253015749651800⟩, ⟨.count 6, 183272308691634480753555120⟩, ⟨.count 7, 30545384781939080125592520⟩, ⟨.count 8, 5588344824970143557280960⟩, ⟨.count 9, 1524094043173675515622080⟩, ⟨.count 10, 346385009812198980823200⟩, ⟨.path 8, 261634660150553609024000⟩, ⟨.path 9, 107297028876636432713880⟩, ⟨.privateRow 2 34, 24251384414979524804578536960⟩, ⟨.privateRow 3 30, 70171829904454643531766600⟩, ⟨.privateRow 3 31, 4409909665995505153507465440⟩, ⟨.privateRow 3 32, 7597270117655622739705930560⟩, ⟨.privateRow 4 28, 731107912510412144843911776⟩, ⟨.privateRow 4 29, 1712192649668693302175105040⟩, ⟨.privateRow 4 30, 2751836466841358569873200000⟩, ⟨.privateRow 4 31, 4528972457127507934297312560⟩, ⟨.privateRow 5 25, 99184048654867823882715480⟩, ⟨.privateRow 5 26, 339026252714855375808378240⟩, ⟨.privateRow 5 27, 604963728870404268000924288⟩, ⟨.privateRow 5 28, 958258253665832087994095070⟩, ⟨.privateRow 5 29, 1620556495322876061798327480⟩, ⟨.privateRow 5 30, 1919405935621847602486557000⟩, ⟨.privateRow 6 22, 9814883398400845565881080⟩, ⟨.privateRow 6 23, 59095688125418175288026970⟩, ⟨.privateRow 6 24, 129611497588227988641027720⟩, ⟨.privateRow 6 25, 222715298049693953588404320⟩, ⟨.privateRow 6 26, 339301436361539511665365560⟩, ⟨.privateRow 6 27, 567015903992661933322372860⟩, ⟨.privateRow 6 28, 708597890211649831742349000⟩, ⟨.privateRow 6 29, 697590544344284397462856200⟩, ⟨.privateRow 7 20, 8361651664245099540171852⟩, ⟨.privateRow 7 21, 25841054821957900475190240⟩, ⟨.privateRow 7 22, 51007254510380896348721100⟩, ⟨.privateRow 7 23, 84964354911924313884921720⟩, ⟨.privateRow 7 24, 127252780616649681295422120⟩, ⟨.privateRow 7 25, 208086011232638274029326032⟩, ⟨.privateRow 7 26, 261817583845192115362221600⟩, ⟨.privateRow 7 27, 270584148589558157663389080⟩, ⟨.privateRow 7 28, 175606478534004981880336920⟩, ⟨.privateRow 8 17, 275183646684135856987320⟩, ⟨.privateRow 8 18, 4352904956639967192344880⟩, ⟨.privateRow 8 19, 11183040041786844095877012⟩, ⟨.privateRow 8 20, 21259700704084649669302440⟩, ⟨.privateRow 8 21, 34696953451625706660333915⟩, ⟨.privateRow 8 22, 51229518225010390694749320⟩, ⟨.privateRow 8 23, 82798525692692108046607860⟩, ⟨.privateRow 8 24, 105124386627904268690032968⟩, ⟨.privateRow 8 25, 106591327144458931373819220⟩, ⟨.privateRow 9 15, 214936339421928598356960⟩, ⟨.privateRow 9 16, 2063877350131018927404900⟩, ⟨.privateRow 9 17, 5141893034545531537553280⟩, ⟨.privateRow 9 18, 9610259661122898390172560⟩, ⟨.privateRow 9 19, 15556108027084397932599440⟩, ⟨.privateRow 9 20, 22782030749523170467892550⟩, ⟨.privateRow 9 21, 36481489160411153612033280⟩, ⟨.privateRow 9 22, 47366867184374461742458440⟩, ⟨.privateRow 9 23, 1744240960520984201211936⟩, ⟨.privateRow 10 13, 121234753434269643288120⟩, ⟨.privateRow 10 14, 996523028228941683291360⟩, ⟨.privateRow 10 15, 2563249072610272458091680⟩, ⟨.privateRow 10 16, 4833645364197503959669200⟩, ⟨.privateRow 10 17, 7835228921951940946220784⟩, ⟨.privateRow 10 18, 11499982325765006163330240⟩, ⟨.privateRow 10 19, 18020680135479651977326980⟩, ⟨.privateRow 11 11, 62349301766195816548176⟩, ⟨.privateRow 11 12, 509680800152235643211280⟩, ⟨.privateRow 11 13, 1406856039852623552881920⟩, ⟨.privateRow 11 14, 2753760828006981897544440⟩, ⟨.privateRow 11 15, 4540792583174463003155040⟩, ⟨.privateRow 11 16, 5032974192571251191361096⟩, ⟨.privateRow 12 9, 34397955835516982123415⟩, ⟨.privateRow 12 10, 285062034001002272366352⟩, ⟨.privateRow 12 11, 858814897343896520707680⟩, ⟨.privateRow 12 12, 1791136161849404986308000⟩, ⟨.privateRow 12 13, 1270078369311396263018400⟩, ⟨.privateRow 13 7, 18677623078108768573800⟩, ⟨.privateRow 13 8, 174635775780316986165030⟩, ⟨.privateRow 13 9, 588469644447613601865192⟩, ⟨.privateRow 13 10, 390095499145643137927080⟩, ⟨.privateRow 14 5, 13103983175435040808920⟩, ⟨.privateRow 14 6, 124873251436498624179120⟩, ⟨.privateRow 14 7, 162161791796008630010385⟩, ⟨.privateRow 15 3, 14483349825480834578280⟩, ⟨.privateRow 15 4, 61151921485363523774960⟩, ⟨.hall 6 29, 25371932224277326014230904⟩, ⟨.hall 5 30, 434346317169508628464179600⟩, ⟨.hall 4 31, 1461637939362787604388150180⟩, ⟨.hall 3 32, 3688061266251094961863514880⟩, ⟨.hall 2 33, 8093701416273803825711055840⟩, ⟨.assumptionRow 18, 5770269053161731168336⟩]
  caps := #[0, 2265747230744033368409788480, 277302986366907279324378800, 23593160286841441418123760, 7169848189966414837930968, 0, 0, 921682557799338634894696, 142016429917533485375198, 0, 80751484622487533952240, 653345403824526894182880, 52149699507700647556704, 635916327545737393875720, 252954792783241317854085, 0, 3552781573418407261382880, 621531527036033088569952, 75359588117101770431664, 4772344539427264800000, 0] }

theorem case_56_36_18_checked :
    (Witness.linear .conditional case_56_36_18).check 56 36 18 = true := by
  change case_56_36_18.check 56 36 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_36_19 : Certificate := {
  objectiveScale := 398618193610837200000
  eta := 196876443986733026353608650880
  rows := #[⟨.count 2, 27242235818768360987328251520⟩, ⟨.count 3, 3696356750751220254715336320⟩, ⟨.count 4, 501062824457804205901624320⟩, ⟨.count 5, 65560811635103954786416800⟩, ⟨.count 6, 9038480827363846193855520⟩, ⟨.count 7, 1591281835803494048214000⟩, ⟨.count 8, 430870158617561465362560⟩, ⟨.count 9, 146887554074168681373600⟩, ⟨.count 10, 53413656026970429590400⟩, ⟨.count 11, 29377510814833736274720⟩, ⟨.path 7, 173087545703531567668560⟩, ⟨.path 8, 9570182266650992179200⟩, ⟨.privateRow 2 34, 2207426162626606943682460800⟩, ⟨.privateRow 3 30, 15870384175746847307520960⟩, ⟨.privateRow 3 31, 374156329961546885007615360⟩, ⟨.privateRow 3 32, 675212708568138594538164480⟩, ⟨.privateRow 4 28, 59373907857499969926960768⟩, ⟨.privateRow 4 29, 141242175745918131719474640⟩, ⟨.privateRow 4 30, 241450497219250163582337600⟩, ⟨.privateRow 4 31, 421116825027036664919352960⟩, ⟨.privateRow 5 25, 6619732436942535240570240⟩, ⟨.privateRow 5 26, 25481726463999951358733520⟩, ⟨.privateRow 5 27, 48947829269315476923062640⟩, ⟨.privateRow 5 28, 83287691285954878483520760⟩, ⟨.privateRow 5 29, 151723418771077145850377520⟩, ⟨.privateRow 5 30, 195377583799952999239714920⟩, ⟨.privateRow 6 22, 384265095164399303494640⟩, ⟨.privateRow 6 23, 3712990950208152779166000⟩, ⟨.privateRow 6 24, 9341582129421654583991520⟩, ⟨.privateRow 6 25, 17649083649989419543635720⟩, ⟨.privateRow 6 26, 29355967306902858201451872⟩, ⟨.privateRow 6 27, 53387505591207225317579700⟩, ⟨.privateRow 6 28, 73877911363570217011748640⟩, ⟨.privateRow 6 29, 81738843632439477609925800⟩, ⟨.privateRow 7 20, 276428387476721251804032⟩, ⟨.privateRow 7 21, 1543795965147770733759360⟩, ⟨.privateRow 7 22, 3538328824897340694350130⟩, ⟨.privateRow 7 23, 6596350336498075736188320⟩, ⟨.privateRow 7 24, 10920739913142836296600080⟩, ⟨.privateRow 7 25, 19677336529592920687629120⟩, ⟨.privateRow 7 26, 27692850462511663564775640⟩, ⟨.privateRow 7 27, 32883460260251632245854640⟩, ⟨.privateRow 7 28, 27697396982042530690627680⟩, ⟨.privateRow 8 18, 127747660664504277437040⟩, ⟨.privateRow 8 19, 616438101931261232831208⟩, ⟨.privateRow 8 20, 1415560798892544107163360⟩, ⟨.privateRow 8 21, 2621942840223910962518760⟩, ⟨.privateRow 8 22, 4326188199755872829979600⟩, ⟨.privateRow 8 23, 7779328072161389108525160⟩, ⟨.privateRow 8 24, 11138972850624458337498000⟩, ⟨.privateRow 8 25, 13530791856132171699198120⟩, ⟨.privateRow 8 26, 11582899680715279241204880⟩, ⟨.privateRow 9 16, 50322587969854085285400⟩, ⟨.privateRow 9 17, 252824638527660033394560⟩, ⟨.privateRow 9 18, 602891805277754565548976⟩, ⟨.privateRow 9 19, 1130127453074344718913920⟩, ⟨.privateRow 9 20, 1865063915758402895996460⟩, ⟨.privateRow 9 21, 3349968852281993038056960⟩, ⟨.privateRow 9 22, 4918556949572440919624880⟩, ⟨.privateRow 9 23, 6189515111898636747124896⟩, ⟨.privateRow 9 24, 987410780165245024789200⟩, ⟨.privateRow 10 14, 18489342470874379473600⟩, ⟨.privateRow 10 15, 108162653454615119920560⟩, ⟨.privateRow 10 16, 276537064612360542288480⟩, ⟨.privateRow 10 17, 534937765110108852347856⟩, ⟨.privateRow 10 18, 894085253384788357532640⟩, ⟨.privateRow 10 19, 1609420223162652756595740⟩, ⟨.privateRow 10 20, 2429558296998197825940480⟩, ⟨.privateRow 10 21, 1052694137531542216510800⟩, ⟨.privateRow 11 12, 6676707003371303698800⟩, ⟨.privateRow 11 13, 48277727562838657514400⟩, ⟨.privateRow 11 14, 137317607369336479405320⟩, ⟨.privateRow 11 15, 281150062178326170298560⟩, ⟨.privateRow 11 16, 484461860164621796384928⟩, ⟨.privateRow 11 17, 883402522179394271614560⟩, ⟨.privateRow 11 18, 539811761222569904047980⟩, ⟨.privateRow 12 10, 2393723103430897029792⟩, ⟨.privateRow 12 11, 22616020230467241417840⟩, ⟨.privateRow 12 12, 73820411791120670639040⟩, ⟨.privateRow 12 13, 164840477349900409097040⟩, ⟨.privateRow 12 14, 300006701351483912866080⟩, ⟨.privateRow 12 15, 219025663963927078225968⟩, ⟨.privateRow 13 8, 918047212963554258585⟩, ⟨.privateRow 13 9, 11098170752270522592672⟩, ⟨.privateRow 13 10, 43366801679040277357920⟩, ⟨.privateRow 13 11, 108094174408426696292880⟩, ⟨.privateRow 13 12, 80380133757253417307220⟩, ⟨.privateRow 14 7, 5683149413583907315050⟩, ⟨.privateRow 14 8, 27885319789318371892512⟩, ⟨.privateRow 14 9, 37021659037060881938040⟩, ⟨.privateRow 15 5, 3744192554831750701680⟩, ⟨.privateRow 15 6, 15912818358034940482140⟩, ⟨.privateRow 16 3, 3536181857341097884920⟩, ⟨.privateRow 16 4, 3744192554831750701680⟩, ⟨.hall 6 29, 11733051402657762782164560⟩, ⟨.hall 5 30, 57635201459360100559183200⟩, ⟨.hall 4 31, 160369383412276130179006920⟩, ⟨.hall 3 32, 366723918639571777453128960⟩, ⟨.hall 2 33, 756940943655006048854435520⟩, ⟨.assumptionRow 19, 395654927285410176384⟩]
  caps := #[0, 0, 1349657096794909569744000, 0, 124835748956588259843288, 140865216091032086820600, 109292003644097314578580, 16510739113071030943248, 3204801647569383254400, 67770407377084098022336, 0, 0, 31641318635290525403088, 1579656442816213681920, 161948781716520791047770, 21843426203530320949560, 0, 257957769554065738789632, 47087322373611049001472, 5982236170487985023616, 398618193610837200000] }

theorem case_56_36_19_checked :
    (Witness.linear .conditional case_56_36_19).check 56 36 19 = true := by
  change case_56_36_19.check 56 36 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_36_20 : Certificate := {
  objectiveScale := 141718370393600000
  eta := 68680904257551230401236480
  rows := #[⟨.count 2, 9346988218685179934551680⟩, ⟨.count 3, 1248903624609076029834240⟩, ⟨.count 4, 160381161403816722969600⟩, ⟨.count 5, 18996760549343210634000⟩, ⟨.count 6, 2263443810134510203200⟩, ⟨.count 7, 355684027306851603360⟩, ⟨.count 8, 89542832049277326720⟩, ⟨.count 9, 37309513353865552800⟩, ⟨.count 10, 13567095765042019200⟩, ⟨.count 11, 7461902670773110560⟩, ⟨.path 7, 72580157076447100080⟩, ⟨.privateRow 2 34, 811347601198501857409920⟩, ⟨.privateRow 3 30, 549693496746952477920⟩, ⟨.privateRow 3 31, 128628278238786879833280⟩, ⟨.privateRow 3 32, 244247143721229217689120⟩, ⟨.privateRow 4 28, 16969361593694156494848⟩, ⟨.privateRow 4 29, 47839501672771540651920⟩, ⟨.privateRow 4 30, 86657563016578390636800⟩, ⟨.privateRow 4 31, 159378779145042868451040⟩, ⟨.privateRow 5 25, 1635222670995135942720⟩, ⟨.privateRow 5 26, 7622955403417296862920⟩, ⟨.privateRow 5 27, 16128653892787052705088⟩, ⟨.privateRow 5 28, 29546025450148695688200⟩, ⟨.privateRow 5 29, 57496861929345450852240⟩, ⟨.privateRow 5 30, 79551966198334696106040⟩, ⟨.privateRow 6 22, 50298751336322448960⟩, ⟨.privateRow 6 23, 947817095493826147590⟩, ⟨.privateRow 6 24, 2741538574111901644080⟩, ⟨.privateRow 6 25, 5672980597146653350560⟩, ⟨.privateRow 6 26, 10239388664894212824000⟩, ⟨.privateRow 6 27, 20133871606339357426560⟩, ⟨.privateRow 6 28, 30360685583399489638320⟩, ⟨.privateRow 6 29, 36799823946436911720360⟩, ⟨.privateRow 7 20, 35337439076589802152⟩, ⟨.privateRow 7 21, 379806897845700124800⟩, ⟨.privateRow 7 22, 998340394827185750340⟩, ⟨.privateRow 7 23, 2058876002221478668800⟩, ⟨.privateRow 7 24, 3726598558828604298840⟩, ⟨.privateRow 7 25, 7334943726760385207472⟩, ⟨.privateRow 7 26, 11367453645438291421020⟩, ⟨.privateRow 7 27, 15022645941209080814640⟩, ⟨.privateRow 7 28, 14775899770750539821400⟩, ⟨.privateRow 8 18, 11871208794411766800⟩, ⟨.privateRow 8 19, 140532500299560248880⟩, ⟨.privateRow 8 20, 379175202381507692160⟩, ⟨.privateRow 8 21, 786608906543998738200⟩, ⟨.privateRow 8 22, 1432685312788437227520⟩, ⟨.privateRow 8 23, 2839253966229168568080⟩, ⟨.privateRow 8 24, 4514202385728706118448⟩, ⟨.privateRow 8 25, 6147985975494478675560⟩, ⟨.privateRow 8 26, 6791989630997035745280⟩, ⟨.privateRow 8 27, 3883920340137404046480⟩, ⟨.privateRow 9 16, 1934567359089324960⟩, ⟨.privateRow 9 17, 50801236364657338560⟩, ⟨.privateRow 9 18, 150647523919941576528⟩, ⟨.privateRow 9 19, 321598792884801592160⟩, ⟨.privateRow 9 20, 591666699270051224820⟩, ⟨.privateRow 9 21, 1182178580269625658720⟩, ⟨.privateRow 9 22, 1938021943659127326000⟩, ⟨.privateRow 9 23, 2739181560411133629792⟩, ⟨.privateRow 9 24, 3178355987600968814640⟩, ⟨.privateRow 10 15, 17128458403365549240⟩, ⟨.privateRow 10 16, 62531977753420943040⟩, ⟨.privateRow 10 17, 141911821702339520832⟩, ⟨.privateRow 10 18, 267271786571327778240⟩, ⟨.privateRow 10 19, 539716028403077826300⟩, ⟨.privateRow 10 20, 913937715429366307680⟩, ⟨.privateRow 10 21, 1352074152117812563440⟩, ⟨.privateRow 10 22, 637924842872275742784⟩, ⟨.privateRow 11 13, 5165932618227538080⟩, ⟨.privateRow 11 14, 26342777610456587280⟩, ⟨.privateRow 11 15, 67588804356754786560⟩, ⟨.privateRow 11 16, 133771564243314309312⟩, ⟨.privateRow 11 17, 275939653310104623840⟩, ⟨.privateRow 11 18, 483242992281090421380⟩, ⟨.privateRow 11 19, 472813287411714369120⟩, ⟨.privateRow 12 11, 1539757693969054560⟩, ⟨.privateRow 12 12, 10905857749591469280⟩, ⟨.privateRow 12 13, 34062203858251328760⟩, ⟨.privateRow 12 14, 74392908444980405280⟩, ⟨.privateRow 12 15, 160430907421621877040⟩, ⟨.privateRow 12 16, 244308220776423323520⟩, ⟨.privateRow 13 9, 414550148376283920⟩, ⟨.privateRow 13 10, 4530440907255102840⟩, ⟨.privateRow 13 11, 17602437069516055680⟩, ⟨.privateRow 13 12, 44875053561732734340⟩, ⟨.privateRow 13 13, 106388642624204500560⟩, ⟨.privateRow 13 14, 7586267715285995736⟩, ⟨.privateRow 14 7, 144352283809598865⟩, ⟨.privateRow 14 8, 1847709232762865472⟩, ⟨.privateRow 14 9, 9403520202453868920⟩, ⟨.privateRow 14 10, 28426295888659468800⟩, ⟨.privateRow 14 11, 20209319733343841100⟩, ⟨.privateRow 15 6, 673643991111461370⟩, ⟨.privateRow 15 7, 5029875133632244896⟩, ⟨.privateRow 15 8, 12318061551752436480⟩, ⟨.privateRow 16 5, 3031397960001576165⟩, ⟨.privateRow 16 6, 2155660771556676384⟩, ⟨.hall 6 29, 8303605292036317431168⟩, ⟨.hall 5 30, 28373884905614752904400⟩, ⟨.hall 4 31, 69617064617422863821280⟩, ⟨.hall 3 32, 147417801400319073624000⟩, ⟨.hall 2 33, 287522033710229496097920⟩, ⟨.assumptionRow 20, 105814551171132804⟩]
  caps := #[0, 11729646329622941319600, 225676919698245315300, 1261975684019864573760, 28983315731794780356, 0, 9056717223317581818, 0, 1507497638833057872, 11615768591276089240, 2352618988717450684, 9565170303484099080, 1723245918471785708, 1396936684493566293, 105814551171132804, 62757454212597732588, 105814551171132804, 327535290899631222408, 79674315162853871460, 15171453258100275136, 2019961004732867196] }

theorem case_56_36_20_checked :
    (Witness.linear .conditional case_56_36_20).check 56 36 20 = true := by
  change case_56_36_20.check 56 36 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_36_21 : Certificate := {
  objectiveScale := 900105598476084000000
  eta := 551402070564346258020445281600
  rows := #[⟨.count 2, 75805611396553713748342389120⟩, ⟨.count 3, 10180130067642704963806172160⟩, ⟨.count 4, 1298485978015651143342624000⟩, ⟨.count 5, 151171774401331934580330000⟩, ⟨.count 6, 15021700529984983815140160⟩, ⟨.count 7, 1145722921778515714714080⟩, ⟨.count 8, 78340028839556630065920⟩, ⟨.path 7, 460776188313231965254080⟩, ⟨.path 8, 36955446473305485731200⟩, ⟨.privateRow 2 34, 6674217927000446876781087360⟩, ⟨.privateRow 3 31, 1041193386075512861235844800⟩, ⟨.privateRow 3 32, 1997504262847410008842069920⟩, ⟨.privateRow 4 28, 138199644875861851099289472⟩, ⟨.privateRow 4 29, 383689876248938484905359680⟩, ⟨.privateRow 4 30, 702794927055399158040540480⟩, ⟨.privateRow 4 31, 1314908006561143201920192480⟩, ⟨.privateRow 5 25, 15285398662775277114558480⟩, ⟨.privateRow 5 26, 60723314854261332879846240⟩, ⟨.privateRow 5 27, 127799026797050214000162768⟩, ⟨.privateRow 5 28, 236655434620695634850386080⟩, ⟨.privateRow 5 29, 470828469577537818985558320⟩, ⟨.privateRow 5 30, 670216083603715623226772520⟩, ⟨.privateRow 6 22, 1284812741500598898187600⟩, ⟨.privateRow 6 23, 8086363862274755588340810⟩, ⟨.privateRow 6 24, 21577781693495379293781840⟩, ⟨.privateRow 6 25, 44191664671191700267845240⟩, ⟨.privateRow 6 26, 80735275221326074030185504⟩, ⟨.privateRow 6 27, 162862391621701604187875520⟩, ⟨.privateRow 6 28, 254555587182556272343851120⟩, ⟨.privateRow 6 29, 321704144471606380080597000⟩, ⟨.privateRow 7 19, 56211514199811737807040⟩, ⟨.privateRow 7 20, 822920035086949779219240⟩, ⟨.privateRow 7 21, 3191656710668722348132080⟩, ⟨.privateRow 7 22, 7747269280597582451876160⟩, ⟨.privateRow 7 23, 15742648627022485200249360⟩, ⟨.privateRow 7 24, 28821902812676999818032240⟩, ⟨.privateRow 7 25, 58402771285706751844965024⟩, ⟨.privateRow 7 26, 94292541810418756608383580⟩, ⟨.privateRow 7 27, 131148902387393112327945840⟩, ⟨.privateRow 7 28, 138177821582113688895199680⟩, ⟨.privateRow 8 17, 41618140321014459722520⟩, ⟨.privateRow 8 18, 366773771385196949854080⟩, ⟨.privateRow 8 19, 1224552575798319573717912⟩, ⟨.privateRow 8 20, 2910005654602697320990320⟩, ⟨.privateRow 8 21, 5901819516405035810356770⟩, ⟨.privateRow 8 22, 10850793458821803591184080⟩, ⟨.privateRow 8 23, 22168596077660368878862320⟩, ⟨.privateRow 8 24, 36864859071174361193270304⟩, ⟨.privateRow 8 25, 53096178608960124099522060⟩, ⟨.privateRow 8 26, 63303639554164229382642480⟩, ⟨.privateRow 8 27, 47836380110154267234002400⟩, ⟨.privateRow 9 15, 18831737701816497612000⟩, ⟨.privateRow 9 16, 153143875821772162246920⟩, ⟨.privateRow 9 17, 490515407847678445071840⟩, ⟨.privateRow 9 18, 1166287179348899330106384⟩, ⟨.privateRow 9 19, 2376676893451919429731360⟩, ⟨.privateRow 9 20, 4387041615015171283691520⟩, ⟨.privateRow 9 21, 9025424155890586755511200⟩, ⟨.privateRow 9 22, 15493372786956481025328720⟩, ⟨.privateRow 9 23, 23205622209423999769359936⟩, ⟨.privateRow 9 24, 29464011263344080053751120⟩, ⟨.privateRow 9 25, 12943513653824523212002560⟩, ⟨.privateRow 10 13, 7821285346806384332880⟩, ⟨.privateRow 10 14, 65329010063756140806720⟩, ⟨.privateRow 10 15, 212096725807095080831880⟩, ⟨.privateRow 10 16, 510100415057567602588320⟩, ⟨.privateRow 10 17, 1048777136089564385007504⟩, ⟨.privateRow 10 18, 1947817989783521665729920⟩, ⟨.privateRow 10 19, 4023717475581716174081820⟩, ⟨.privateRow 10 20, 7117751191708288103132160⟩, ⟨.privateRow 10 21, 11141198419625582105397600⟩, ⟨.privateRow 10 22, 12848654957287736837970720⟩, ⟨.privateRow 11 11, 3382864881708127207392⟩, ⟨.privateRow 11 12, 29568273872072916380400⟩, ⟨.privateRow 11 13, 101280509312678545338720⟩, ⟨.privateRow 11 14, 249263728125862004755200⟩, ⟨.privateRow 11 15, 519569199535075996924800⟩, ⟨.privateRow 11 16, 972929744531266374989136⟩, ⟨.privateRow 11 17, 2015475287417684209877760⟩, ⟨.privateRow 11 18, 3656498590396294470647820⟩, ⟨.privateRow 11 19, 5980040318333817952856640⟩, ⟨.privateRow 11 20, 1694993351255861632335360⟩, ⟨.privateRow 12 9, 1632083934157429793040⟩, ⟨.privateRow 12 10, 14797561003027363456896⟩, ⟨.privateRow 12 11, 54325079522668734539760⟩, ⟨.privateRow 12 12, 139103769157417862360640⟩, ⟨.privateRow 12 13, 296223234049573507436760⟩, ⟨.privateRow 12 14, 561436873350155848805760⟩, ⟨.privateRow 12 15, 1165634345775236358189168⟩, ⟨.privateRow 12 16, 2158340331593525488529120⟩, ⟨.privateRow 12 17, 1371358525675780383601860⟩, ⟨.privateRow 13 7, 1152059247640538677440⟩, ⟨.privateRow 13 8, 8568440654326506413460⟩, ⟨.privateRow 13 9, 33294512256811567778016⟩, ⟨.privateRow 13 10, 90230926074132189986640⟩, ⟨.privateRow 13 11, 198486515377145884830480⟩, ⟨.privateRow 13 12, 383539724526996001364400⟩, ⟨.privateRow 13 13, 799869499003882183116240⟩, ⟨.privateRow 13 14, 571392585348516170543304⟩, ⟨.privateRow 14 5, 505168836763013983560⟩, ⟨.privateRow 14 6, 5883731157592751102640⟩, ⟨.privateRow 14 7, 23869227537052410723210⟩, ⟨.privateRow 14 8, 68500894265064696170736⟩, ⟨.privateRow 14 9, 109765971530934895570680⟩, ⟨.privateRow 14 10, 412684080494092961954400⟩, ⟨.privateRow 14 11, 96992416658498684843520⟩, ⟨.privateRow 15 3, 1116689007581399332080⟩, ⟨.privateRow 15 4, 4714909143121463846560⟩, ⟨.privateRow 15 5, 21217091144046587309520⟩, ⟨.privateRow 15 6, 62325205235636850221715⟩, ⟨.privateRow 15 7, 144276219779516793704736⟩, ⟨.privateRow 16 2, 3350067022744197996240⟩, ⟨.privateRow 16 3, 21217091144046587309520⟩, ⟨.privateRow 16 4, 44930310657981008420160⟩, ⟨.privateRow 17 0, 12730254686427952385712⟩, ⟨.privateRow 17 1, 13400268090976791984960⟩, ⟨.hall 7 28, 5612286419516599008666480⟩, ⟨.hall 6 29, 85258759053236806444575168⟩, ⟨.hall 5 30, 258814290842619902938548000⟩, ⟨.hall 4 31, 604591620695179528678427160⟩, ⟨.hall 3 32, 1245628417496428172558070720⟩, ⟨.hall 2 33, 2389214199548798103750428160⟩, ⟨.assumptionRow 21, 324277764328057379840⟩]
  caps := #[0, 0, 12429777503811890661503680, 0, 0, 267531300639659045768632, 0, 38964733488634156356248, 0, 64463354330272373426720, 2342672044804489798400, 9989329984915494567480, 59771044701130597472484, 0, 139338323518411299265698, 0, 1205694767016607553605920, 0, 1804840805230830453166080, 451068391615950867799040, 88746815776591875302400] }

theorem case_56_36_21_checked :
    (Witness.linear .conditional case_56_36_21).check 56 36 21 = true := by
  change case_56_36_21.check 56 36 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_36_22 : Certificate := {
  objectiveScale := 717927388983925120000
  eta := 716258330061110491557592609920
  rows := #[⟨.count 2, 82837453925312878385524170240⟩, ⟨.count 3, 9928717821507933472554129600⟩, ⟨.count 4, 1238095820384733956867020800⟩, ⟨.count 5, 155683179795401814516760800⟩, ⟨.count 6, 18239804496739384185987360⟩, ⟨.count 7, 1750284269889132825928080⟩, ⟨.count 8, 113378738130470142570240⟩, ⟨.path 4, 66429393685094529579409920⟩, ⟨.path 5, 6427779176970741189600⟩, ⟨.path 8, 109837171925212678934400⟩, ⟨.privateRow 2 34, 7798898225727051844372171200⟩, ⟨.privateRow 4 28, 126315252151156785837504384⟩, ⟨.privateRow 5 25, 11172867256660705031676240⟩, ⟨.privateRow 5 26, 56838178659031313347243440⟩, ⟨.privateRow 5 29, 1075841397891853643670459840⟩, ⟨.privateRow 6 22, 617546691715269086730960⟩, ⟨.privateRow 6 23, 6663362922209505670638480⟩, ⟨.privateRow 6 24, 19889195187161223640997280⟩, ⟨.privateRow 6 25, 34780502626217972763179040⟩, ⟨.privateRow 6 26, 58508625400820240114444976⟩, ⟨.privateRow 6 28, 657912409448326261123854960⟩, ⟨.privateRow 6 30, 1561345688965837487718685680⟩, ⟨.privateRow 7 21, 3790089246075716194490880⟩, ⟨.privateRow 7 22, 6399065610778878470733300⟩, ⟨.privateRow 7 23, 14391435108486908466680400⟩, ⟨.privateRow 7 24, 26692931785151311392913200⟩, ⟨.privateRow 7 25, 54414100745395386531183648⟩, ⟨.privateRow 7 26, 60947398683639446617138500⟩, ⟨.privateRow 7 27, 240025825552690929414302640⟩, ⟨.privateRow 8 17, 21849027660559350391140⟩, ⟨.privateRow 8 18, 94052816858230913723040⟩, ⟨.privateRow 8 19, 1179138876556889482730496⟩, ⟨.privateRow 8 20, 2715578248694385567533040⟩, ⟨.privateRow 8 21, 5216307725393270856219870⟩, ⟨.privateRow 8 22, 10350871405214796498042000⟩, ⟨.privateRow 8 23, 22130112448841140952928720⟩, ⟨.privateRow 8 24, 38979610169255635015648512⟩, ⟨.privateRow 8 25, 52478411869358078646222180⟩, ⟨.privateRow 8 26, 105794172960950566991218320⟩, ⟨.privateRow 8 27, 96417987523265124680123160⟩, ⟨.privateRow 9 14, 674873441252798467680⟩, ⟨.privateRow 9 15, 13445555483421138702240⟩, ⟨.privateRow 9 16, 55902016717106806406160⟩, ⟨.privateRow 9 17, 393389864119358524978560⟩, ⟨.privateRow 9 18, 1073318720968450682998272⟩, ⟨.privateRow 9 19, 2164169154221890730634720⟩, ⟨.privateRow 9 20, 3999553090404553518897060⟩, ⟨.privateRow 9 21, 8933974615304546115147840⟩, ⟨.privateRow 9 22, 16458813485273249029779840⟩, ⟨.privateRow 9 23, 26917057254991365764029728⟩, ⟨.privateRow 9 24, 3402543172436296674425640⟩, ⟨.privateRow 9 25, 115419555416818605136504320⟩, ⟨.privateRow 10 12, 515357900593046102592⟩, ⟨.privateRow 10 13, 6902114740085438874000⟩, ⟨.privateRow 10 14, 28245577244041949853600⟩, ⟨.privateRow 10 15, 145588606917535523982240⟩, ⟨.privateRow 10 16, 433603397271694698135360⟩, ⟨.privateRow 10 17, 948516216041501351820576⟩, ⟨.privateRow 10 18, 1780991011466135156207520⟩, ⟨.privateRow 10 19, 3773869276436515413136980⟩, ⟨.privateRow 10 20, 7330045853970736084188000⟩, ⟨.privateRow 10 22, 44151999738557742224313120⟩, ⟨.privateRow 10 24, 33258622114772230230774720⟩, ⟨.privateRow 10 25, 20699994274695438018235920⟩, ⟨.privateRow 11 10, 241574015902990360590⟩, ⟨.privateRow 11 11, 3607505304151322718144⟩, ⟨.privateRow 11 12, 14908567838584547967840⟩, ⟨.privateRow 11 13, 61545626205438774944160⟩, ⟨.privateRow 11 14, 188749831092203135074320⟩, ⟨.privateRow 11 15, 444144808874734277506560⟩, ⟨.privateRow 11 16, 876237270483326635932048⟩, ⟨.privateRow 11 17, 1864307205395344276126560⟩, ⟨.privateRow 11 18, 3526980632183659264614000⟩, ⟨.privateRow 11 19, 6364854128717188312047840⟩, ⟨.privateRow 11 20, 2668909727696237503798320⟩, ⟨.privateRow 11 21, 23260678843267135840489920⟩, ⟨.privateRow 11 22, 17548902811256831754699960⟩, ⟨.privateRow 12 8, 277889064045269957280⟩, ⟨.privateRow 12 9, 2066799913836695307270⟩, ⟨.privateRow 12 10, 8818346299036566644352⟩, ⟨.privateRow 12 11, 31044178297628729513280⟩, ⟨.privateRow 12 12, 93392101601060341796640⟩, ⟨.privateRow 12 13, 229513209479389212216840⟩, ⟨.privateRow 12 14, 477994452800050260154080⟩, ⟨.privateRow 12 15, 1053477441795618408048480⟩, ⟨.privateRow 12 16, 2024020436255059582179840⟩, ⟨.privateRow 12 18, 13353720782069123279984160⟩, ⟨.privateRow 12 19, 673186257649666471510800⟩, ⟨.privateRow 12 20, 1060091201519895833031744⟩, ⟨.privateRow 13 7, 1667334384271619743680⟩, ⟨.privateRow 13 8, 6200399741510085921810⟩, ⟨.privateRow 13 9, 19368867763955316022416⟩, ⟨.privateRow 13 10, 55170903822416274732840⟩, ⟨.privateRow 13 11, 136817611878596181659280⟩, ⟨.privateRow 13 12, 297028673331387925587660⟩, ⟨.privateRow 13 14, 2732427588944330435942784⟩, ⟨.privateRow 13 15, 1816421867131907075760720⟩, ⟨.privateRow 13 16, 634212316417317360002280⟩, ⟨.privateRow 13 17, 11812647278968357979036880⟩, ⟨.privateRow 14 5, 1462225789381063346640⟩, ⟨.privateRow 14 6, 4644717213328083571680⟩, ⟨.privateRow 14 7, 14805036117483266384730⟩, ⟨.privateRow 14 8, 41234767260545986375248⟩, ⟨.privateRow 14 9, 99640243076395316621040⟩, ⟨.privateRow 14 10, 217646684804027505826800⟩, ⟨.privateRow 14 11, 516531260098860627200580⟩, ⟨.privateRow 14 12, 16749131769273998334240⟩, ⟨.privateRow 14 13, 3934849599224441465808240⟩, ⟨.privateRow 14 15, 7864764186409721842821570⟩, ⟨.privateRow 14 16, 9007101973188867206252880⟩, ⟨.privateRow 15 3, 1616144293526438435760⟩, ⟨.privateRow 15 4, 5117790262833721713240⟩, ⟨.privateRow 15 5, 14450231330354037778560⟩, ⟨.privateRow 15 6, 38383426971252912849300⟩, ⟨.privateRow 15 8, 381640931028457533473040⟩, ⟨.privateRow 15 9, 382653241190336731174560⟩, ⟨.privateRow 15 11, 223321756923653311123200⟩, ⟨.privateRow 15 12, 9506807192239921454514624⟩, ⟨.privateRow 15 14, 10486352248546295790428760⟩, ⟨.privateRow 15 15, 17002761478923004594729920⟩, ⟨.privateRow 16 2, 9696865761158630614560⟩, ⟨.privateRow 16 3, 15353370788501165139720⟩, ⟨.privateRow 16 4, 48769530739944877502640⟩, ⟨.privateRow 16 5, 86362710685319053910925⟩, ⟨.privateRow 16 6, 18424044946201398167664⟩, ⟨.privateRow 16 7, 1059382584406580394640680⟩, ⟨.privateRow 16 10, 3651310725701731636864320⟩, ⟨.privateRow 16 11, 17069877642655595402340696⟩, ⟨.privateRow 16 12, 7605036330570910465874640⟩, ⟨.privateRow 16 13, 16754365872951896458719450⟩, ⟨.privateRow 16 18, 145427128108683036203427840⟩, ⟨.privateRow 17 0, 18424044946201398167664⟩, ⟨.privateRow 17 1, 38787463044634522458240⟩, ⟨.privateRow 17 2, 81884644205339547411840⟩, ⟨.privateRow 17 3, 173402775964248453342720⟩, ⟨.privateRow 17 4, 299390730375772720224540⟩, ⟨.privateRow 17 5, 73696179784805592670656⟩, ⟨.privateRow 17 8, 11668561799260885506187200⟩, ⟨.privateRow 17 9, 2344878447698359766793600⟩, ⟨.privateRow 17 10, 46354897084642717789842624⟩, ⟨.privateRow 17 16, 359084636001465250287771360⟩, ⟨.privateRow 18 0, 439591247839191254526720⟩, ⟨.privateRow 18 1, 348009737872693076500320⟩, ⟨.privateRow 18 2, 859788764156065247824320⟩, ⟨.privateRow 18 3, 1566043820427118844251440⟩, ⟨.privateRow 18 4, 417611685447231691800384⟩, ⟨.privateRow 18 6, 160619879018166035307840⟩, ⟨.privateRow 18 7, 174004868936346538250160⟩, ⟨.privateRow 18 8, 189823493385105314454720⟩, ⟨.privateRow 18 9, 417611685447231691800384⟩, ⟨.privateRow 18 10, 384898770087198542609353920⟩, ⟨.privateRow 18 12, 10141998075147055372295040⟩, ⟨.privateRow 18 15, 426485933762985365251142160⟩, ⟨.privateRow 18 18, 5537530949030292233273091840⟩, ⟨.privateRow 19 0, 10440292136180792295009600⟩, ⟨.privateRow 19 2, 19967058710445765264205860⟩, ⟨.privateRow 19 9, 1728912377751539204053589760⟩, ⟨.privateRow 19 10, 1533939922108362907944285480⟩, ⟨.hall 18 4, 128968314623409787173648⟩, ⟨.hall 18 11, 465325237743804543465360⟩, ⟨.hall 16 13, 8603591680243686966840⟩, ⟨.hall 13 14, 19340910384879787704⟩, ⟨.hall 14 14, 147306318851429385648⟩, ⟨.hall 10 19, 26617945686604957944⟩, ⟨.hall 8 20, 19743941087291762880⟩, ⟨.hall 4 26, 2871319162240308299520⟩, ⟨.hall 4 29, 2344212084391410156107184⟩, ⟨.hall 3 32, 5101506384724705325970600000⟩, ⟨.hall 2 33, 7021772009896276869660103680⟩]
  caps := #[0, 0, 17222826130033889439412800, 2686863017712756595426560, 2144711200411497215680, 0, 264604201711930594011456, 77966966721255898929132, 0, 22217059228506304745968, 0, 6898448527850131576422, 66889511598176026712106, 60342308816358810635240, 11581462033973914426344, 51616098970982950193790, 1873120191615474015737523, 2491352785261431825717984, 0, 0, 315888051152927052800000] }

theorem case_56_36_22_checked :
    (Witness.linear .conditional case_56_36_22).check 56 36 22 = true := by
  change case_56_36_22.check 56 36 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_36_23 : Certificate := {
  objectiveScale := 744299891110155219840000
  eta := 662200580582443754430728044896000
  rows := #[⟨.count 2, 74099790367234552841333183971200⟩, ⟨.count 3, 7787128617324694544220994680000⟩, ⟨.count 4, 758656981986736536836029497600⟩, ⟨.count 5, 68709958388159069507832306000⟩, ⟨.count 6, 5942482887624568173650361600⟩, ⟨.count 7, 495206907302047347804196800⟩, ⟨.path 5, 13039645340503460299943322000⟩, ⟨.path 7, 79681722223282579672272000⟩, ⟨.path 8, 27076989401655815452208000⟩, ⟨.privateRow 2 34, 7677687890810942080356267187200⟩, ⟨.privateRow 3 33, 12650225515999900182107475321600⟩, ⟨.privateRow 5 25, 7923310516832757564867148800⟩, ⟨.privateRow 5 26, 27318914386162945353864856800⟩, ⟨.privateRow 6 22, 408087173610020499579384400⟩, ⟨.privateRow 6 23, 3935863231994397149735439150⟩, ⟨.privateRow 6 24, 11277747781771625908921767600⟩, ⟨.privateRow 6 25, 22903319462719689835944102000⟩, ⟨.privateRow 6 29, 1104785976569730047645004552600⟩, ⟨.privateRow 7 20, 270595202918618729335864680⟩, ⟨.privateRow 7 21, 1436493052530938933511380400⟩, ⟨.privateRow 7 22, 3974919729147683622106901100⟩, ⟨.privateRow 7 23, 9151221521673548437483677600⟩, ⟨.privateRow 7 24, 19575411139243431171236136600⟩, ⟨.privateRow 8 17, 4761604877904301421194200⟩, ⟨.privateRow 8 18, 114278517069703234108660800⟩, ⟨.privateRow 8 19, 499016191204370788941152160⟩, ⟨.privateRow 8 20, 1371342204836438809303929600⟩, ⟨.privateRow 8 21, 3181942459659549424713024150⟩, ⟨.privateRow 8 22, 6747874341258667156892352000⟩, ⟨.privateRow 8 23, 16398967199502414094592824800⟩, ⟨.privateRow 8 24, 14837160799549803228441127200⟩, ⟨.privateRow 8 25, 25795994426046552949319578500⟩, ⟨.privateRow 8 26, 35737431810297750266536202400⟩, ⟨.privateRow 9 15, 2930218386402647028427200⟩, ⟨.privateRow 9 16, 44441645527106813264479200⟩, ⟨.privateRow 9 17, 180652403246551072101064800⟩, ⟨.privateRow 9 18, 500920833155532509509629840⟩, ⟨.privateRow 9 19, 1180172586775392041134503200⟩, ⟨.privateRow 9 20, 2564917827564450365549942400⟩, ⟨.privateRow 9 21, 6401410900618773224912126400⟩, ⟨.privateRow 9 22, 13861560866788077470587560000⟩, ⟨.privateRow 9 23, 19497184773392146219316517600⟩, ⟨.privateRow 9 24, 34401008041232609667654363600⟩, ⟨.privateRow 9 27, 452365161013916379817238851200⟩, ⟨.privateRow 10 13, 1484136585320821222190400⟩, ⟨.privateRow 10 14, 17581310318415882170563200⟩, ⟨.privateRow 10 15, 70558326827127375604968600⟩, ⟨.privateRow 10 16, 195973490016226620475596000⟩, ⟨.privateRow 10 17, 461269650717711235856776320⟩, ⟨.privateRow 10 18, 990990978831719459417023200⟩, ⟨.privateRow 10 19, 2478415338949188889731581100⟩, ⟨.privateRow 10 20, 5447523336420074296049863200⟩, ⟨.privateRow 10 21, 10850398897231747220332165200⟩, ⟨.privateRow 10 23, 56273079320243752768529527800⟩, ⟨.privateRow 11 11, 692597073149716570355520⟩, ⟨.privateRow 11 12, 7791717072934311416499600⟩, ⟨.privateRow 11 13, 30767293057227793798485600⟩, ⟨.privateRow 11 14, 86141760972995998437967800⟩, ⟨.privateRow 11 15, 204001319727734698904716800⟩, ⟨.privateRow 11 16, 437894499498908301607277520⟩, ⟨.privateRow 11 17, 1085645912162180724032277600⟩, ⟨.privateRow 11 18, 2460883975535086689044457000⟩, ⟨.privateRow 11 20, 19896582418908482774888200800⟩, ⟨.privateRow 11 21, 1839884124822222069149438880⟩, ⟨.privateRow 11 22, 28382628057675385053169209600⟩, ⟨.privateRow 11 25, 128547748269270269749410400800⟩, ⟨.privateRow 12 9, 396800406492025118432850⟩, ⟨.privateRow 12 10, 3809283902323441136955360⟩, ⟨.privateRow 12 11, 14965043901984947323753200⟩, ⟨.privateRow 12 12, 42488166602838381912194400⟩, ⟨.privateRow 12 13, 96819299184054128897615400⟩, ⟨.privateRow 12 14, 199121658530543513977212000⟩, ⟨.privateRow 12 15, 476795368440817382308912560⟩, ⟨.privateRow 12 16, 1066599492650563518347500800⟩, ⟨.privateRow 12 17, 2254619909687686722935453700⟩, ⟨.privateRow 12 18, 379114445516951998868414400⟩, ⟨.privateRow 12 19, 12746287190941158871045629600⟩, ⟨.privateRow 12 20, 8393122198119315305091643200⟩, ⟨.privateRow 13 8, 2380802438952150710597100⟩, ⟨.privateRow 13 9, 8888329105421362652895840⟩, ⟨.privateRow 13 10, 25848712194337636286482800⟩, ⟨.privateRow 13 11, 60802031517854925839864400⟩, ⟨.privateRow 13 12, 127769730890432088135377700⟩, ⟨.privateRow 13 13, 297816741454378125252873600⟩, ⟨.privateRow 13 14, 669481645833344779819904520⟩, ⟨.privateRow 13 15, 1444353479630971431095574000⟩, ⟨.privateRow 13 16, 2935529407228001826166224300⟩, ⟨.privateRow 13 17, 2005315882865982941382928800⟩, ⟨.privateRow 13 18, 11237387511854151354018312000⟩, ⟨.privateRow 13 19, 15589494370258682852989810800⟩, ⟨.privateRow 13 20, 9527971360686507143809594200⟩, ⟨.privateRow 14 6, 1040350645592536444966800⟩, ⟨.privateRow 14 7, 6632235365652419836663350⟩, ⟨.privateRow 14 8, 18865025040077994202064640⟩, ⟨.privateRow 14 9, 45478185364473736022834400⟩, ⟨.privateRow 14 10, 96592556094630114544225200⟩, ⟨.privateRow 14 11, 222548342269670087852481300⟩, ⟨.privateRow 14 12, 480736575595169340887840400⟩, ⟨.privateRow 14 13, 1027554332651748246693708360⟩, ⟨.privateRow 14 14, 2110524676358725601355981600⟩, ⟨.privateRow 14 15, 4083246240120006479439069150⟩, ⟨.privateRow 14 16, 3842906663298030693929506800⟩, ⟨.privateRow 14 18, 20536937884254906438222618720⟩, ⟨.privateRow 14 22, 194722430335555046404435956000⟩, ⟨.privateRow 15 4, 2292624570842811795389800⟩, ⟨.privateRow 15 5, 4854969679431836743178400⟩, ⟨.privateRow 15 6, 18054418495387142888694675⟩, ⟨.privateRow 15 7, 41267242275170612317016400⟩, ⟨.privateRow 15 8, 91377465037877784416250600⟩, ⟨.privateRow 15 9, 209510614627789262532544800⟩, ⟨.privateRow 15 10, 450500728170612517794095700⟩, ⟨.privateRow 15 11, 926637167451558294754822800⟩, ⟨.privateRow 15 12, 1894166420430331105351052760⟩, ⟨.privateRow 15 13, 3714051804765355108531476000⟩, ⟨.privateRow 15 14, 6901946270522284910020992900⟩, ⟨.privateRow 15 15, 7940996477807830684431584400⟩, ⟨.privateRow 15 16, 3844731405303395380868694600⟩, ⟨.privateRow 15 17, 16936076229730019294903530560⟩, ⟨.privateRow 15 18, 22851735409875726570547831500⟩, ⟨.privateRow 16 3, 6877873712528435386169400⟩, ⟨.privateRow 16 4, 21847363557443265344302800⟩, ⟨.privateRow 16 5, 46425647559566938856643450⟩, ⟨.privateRow 16 6, 107294829915443592024242640⟩, ⟨.privateRow 16 7, 256446434138560233684316200⟩, ⟨.privateRow 16 8, 552346165836898964858527200⟩, ⟨.privateRow 16 9, 1124532351998399185638696900⟩, ⟨.privateRow 16 10, 2228431082859213065118885600⟩, ⟨.privateRow 16 11, 4357820784258016660676931840⟩, ⟨.privateRow 16 12, 8212181212758951851086263600⟩, ⟨.privateRow 16 13, 14701455060529530637937092500⟩, ⟨.privateRow 16 15, 52450664931741848254927844400⟩, ⟨.privateRow 17 2, 27511494850113741544677600⟩, ⟨.privateRow 17 3, 58259636153182040918140800⟩, ⟨.privateRow 17 4, 185702590238267755426573800⟩, ⟨.privateRow 17 5, 429179319661774368096970560⟩, ⟨.privateRow 17 6, 884298048753655978221780000⟩, ⟨.privateRow 17 8, 7345569124980368992428919200⟩, ⟨.privateRow 17 9, 5132144312039399786334403200⟩, ⟨.privateRow 17 10, 13122983043504254716811215200⟩, ⟨.privateRow 17 11, 23879977529898727660780156800⟩, ⟨.privateRow 17 12, 41411677623133709460125957400⟩, ⟨.privateRow 17 14, 124296933732813884298853396800⟩, ⟨.privateRow 18 0, 147693288142715875660900800⟩, ⟨.privateRow 18 1, 155898470817311202086506400⟩, ⟨.privateRow 18 2, 330137938201364898536131200⟩, ⟨.privateRow 18 3, 876928898347375511736598500⟩, ⟨.privateRow 18 4, 2057859814788507867541884480⟩, ⟨.privateRow 18 5, 4409699603118231144732609600⟩, ⟨.privateRow 18 6, 647578263394984993282411200⟩, ⟨.privateRow 18 9, 1964320732298121146289980640⟩, ⟨.privateRow 18 14, 39286414645962422925799612800⟩, ⟨.privateRow 18 18, 10399675191281195668786668931200⟩, ⟨.privateRow 19 1, 7428103609530710217062952000⟩, ⟨.privateRow 19 2, 4735416051075827763377631900⟩, ⟨.privateRow 19 3, 15153331363442648842808422080⟩, ⟨.privateRow 19 5, 54396574125178739435722540800⟩, ⟨.privateRow 19 9, 8418517424134804912671345600⟩, ⟨.hall 11 11, 30966348589018236998604⟩, ⟨.hall 16 11, 6751749331517554337173200⟩, ⟨.hall 15 12, 1277483201652697586066520⟩, ⟨.hall 9 15, 7358803562812604613480⟩, ⟨.hall 12 15, 38966742888416421828750⟩, ⟨.hall 18 15, 8139963538777403279531484900⟩, ⟨.hall 7 18, 18695004563902758010920⟩, ⟨.hall 14 18, 6456645083244397238116920⟩, ⟨.hall 5 26, 34131070323213040817239600⟩, ⟨.hall 9 26, 306858981020499424921404000⟩, ⟨.hall 4 31, 3316400658201811088244705969600⟩, ⟨.hall 3 32, 5041926617290917705879893164800⟩]
  caps := #[0, 156763443750028092925554992000, 0, 2385732313197007528902876000, 2116273181679167030912492800, 136396593311476098230168000, 170801744028428730076446300, 72667582049811533773705480, 81476956854448693585495070, 930110615405643082118400, 54694748795008665353631180, 369759403554267142578456, 0, 336530688139278795568703220, 286456669696472340576804150, 399268683035393161724583850, 0, 2299660035860763389858444400, 2264627535417818376490424740, 0, 937817862798795576998400000] }

theorem case_56_36_23_checked :
    (Witness.linear .conditional case_56_36_23).check 56 36 23 = true := by
  change case_56_36_23.check 56 36 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_37_1_checked :
    (Witness.rising).check 56 37 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_37_2_checked :
    (Witness.rising).check 56 37 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_37_3_checked :
    (Witness.rising).check 56 37 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_37_4_checked :
    (Witness.rising).check 56 37 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_37_5_checked :
    (Witness.rising).check 56 37 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_37_6_checked :
    (Witness.rising).check 56 37 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_37_7_checked :
    (Witness.rising).check 56 37 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_37_8_checked :
    (Witness.rising).check 56 37 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_37_9_checked :
    (Witness.rising).check 56 37 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_37_10_checked :
    (Witness.rising).check 56 37 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_37_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_37_11_checked :
    (Witness.linear .positive case_56_37_11).check 56 37 11 = true := by
  change case_56_37_11.check 56 37 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_37_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_37_12_checked :
    (Witness.linear .positive case_56_37_12).check 56 37 12 = true := by
  change case_56_37_12.check 56 37 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_37_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_37_13_checked :
    (Witness.linear .positive case_56_37_13).check 56 37 13 = true := by
  change case_56_37_13.check 56 37 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_37_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_56_37_14_checked :
    (Witness.linear .positive case_56_37_14).check 56 37 14 = true := by
  change case_56_37_14.check 56 37 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_37_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_56_37_15_checked :
    (Witness.linear .positive case_56_37_15).check 56 37 15 = true := by
  change case_56_37_15.check 56 37 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_37_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_56_37_16_checked :
    (Witness.linear .positive case_56_37_16).check 56 37 16 = true := by
  change case_56_37_16.check 56 37 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_37_17 : Certificate := {
  objectiveScale := 615
  eta := 8435085435
  rows := #[⟨.assumptionRow 17, 1883⟩]
  caps := #[0, 0, 2363202045, 667867100, 190657856, 55073438, 16132558, 4805866, 1461460, 456027, 147081, 49566, 17752, 3407404, 1498266, 411488, 78575, 9802, 615, 0] }

theorem case_56_37_17_checked :
    (Witness.linear .conditional case_56_37_17).check 56 37 17 = true := by
  change case_56_37_17.check 56 37 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_37_18 : Certificate := {
  objectiveScale := 132058923045878400000
  eta := 123072709460249593142133235200
  rows := #[⟨.count 2, 17455089310230564385538745600⟩, ⟨.count 3, 2468582975162534401211040000⟩, ⟨.count 4, 346203709931331044072280000⟩, ⟨.count 5, 47565379277522004316017600⟩, ⟨.count 6, 6278974118009233842801600⟩, ⟨.count 7, 879982674072948473227200⟩, ⟨.count 8, 154382925275955872496000⟩, ⟨.count 9, 50525320999403740089600⟩, ⟨.count 10, 25262660499701870044800⟩, ⟨.path 8, 30050731701827220384000⟩, ⟨.privateRow 2 35, 1241918004089899420706822400⟩, ⟨.privateRow 3 31, 43551423220347151631121600⟩, ⟨.privateRow 3 32, 242710542923839425680044800⟩, ⟨.privateRow 3 33, 389353737545960710434912000⟩, ⟨.privateRow 4 28, 11264164185446930346989400⟩, ⟨.privateRow 4 29, 49763020218825236160998160⟩, ⟨.privateRow 4 30, 93286847491279310679911100⟩, ⟨.privateRow 4 31, 139484972986826130800136000⟩, ⟨.privateRow 4 32, 217807290552450443814169200⟩, ⟨.privateRow 5 25, 1931716352515397854606200⟩, ⟨.privateRow 5 26, 9839926563017210296116480⟩, ⟨.privateRow 5 27, 20732083035308114117487840⟩, ⟨.privateRow 5 28, 33187388680721681998720128⟩, ⟨.privateRow 5 29, 48498624060815157565255920⟩, ⟨.privateRow 5 30, 77174995125948500954933760⟩, ⟨.privateRow 5 31, 83269518406092318948167520⟩, ⟨.privateRow 6 22, 217900471675206288608640⟩, ⟨.privateRow 6 23, 1753716515456155875424800⟩, ⟨.privateRow 6 24, 4515700564321709270508000⟩, ⟨.privateRow 6 25, 7968521948197628467821600⟩, ⟨.privateRow 6 26, 12309465242002881567014400⟩, ⟨.privateRow 6 27, 17348891501403595425932640⟩, ⟨.privateRow 6 28, 27147961725981704542935000⟩, ⟨.privateRow 6 29, 30701985318271938691020000⟩, ⟨.privateRow 6 30, 25574634307142632820908800⟩, ⟨.privateRow 7 20, 250220637330380427110400⟩, ⟨.privateRow 7 21, 921666063897456558801120⟩, ⟨.privateRow 7 22, 1922434998079164793224000⟩, ⟨.privateRow 7 23, 3218883992003679941541600⟩, ⟨.privateRow 7 24, 4827144486026367188798400⟩, ⟨.privateRow 7 25, 6666034166379666065988000⟩, ⟨.privateRow 7 26, 10185303221563134433728960⟩, ⟨.privateRow 7 27, 11641575300987615328144800⟩, ⟨.privateRow 7 28, 8493266360538658071172800⟩, ⟨.privateRow 8 17, 8312926745628393134400⟩, ⟨.privateRow 8 18, 157920867313529861240700⟩, ⟨.privateRow 8 19, 448412223869708193295200⟩, ⟨.privateRow 8 20, 865702253484922555021320⟩, ⟨.privateRow 8 21, 1410888400438596723644000⟩, ⟨.privateRow 8 22, 2074520558395657036665000⟩, ⟨.privateRow 8 23, 2816937018695923402078800⟩, ⟨.privateRow 8 24, 4239097823202288332286000⟩, ⟨.privateRow 8 25, 4155216433802352308229840⟩, ⟨.privateRow 9 15, 7017405694361630568000⟩, ⟨.privateRow 9 16, 89606872712617744176000⟩, ⟨.privateRow 9 17, 230404820298206870316000⟩, ⟨.privateRow 9 18, 431506655606018810563200⟩, ⟨.privateRow 9 19, 692196897691831239227520⟩, ⟨.privateRow 9 20, 1006763803617748598822400⟩, ⟨.privateRow 9 21, 1355762780150667025737600⟩, ⟨.privateRow 9 22, 1478066136538112587065600⟩, ⟨.privateRow 10 13, 4715696626611015741696⟩, ⟨.privateRow 10 14, 51968901599386704092160⟩, ⟨.privateRow 10 15, 131754490913829753002880⟩, ⟨.privateRow 10 16, 245258329017938988351600⟩, ⟨.privateRow 10 17, 392030558845373565149760⟩, ⟨.privateRow 10 18, 568662487848289094708448⟩, ⟨.privateRow 10 19, 265538631474644100693120⟩, ⟨.privateRow 11 11, 3157832562462733755600⟩, ⟨.privateRow 11 12, 32373631603321655687040⟩, ⟨.privateRow 11 13, 86013344082318271819200⟩, ⟨.privateRow 11 14, 162803812109189829177600⟩, ⟨.privateRow 11 15, 215668268340047446123200⟩, ⟨.privateRow 12 9, 2270337136411115772000⟩, ⟨.privateRow 12 10, 22433768829162337722075⟩, ⟨.privateRow 12 11, 64840828615901466448320⟩, ⟨.privateRow 12 12, 55136759027127097320000⟩, ⟨.privateRow 13 7, 1837891967570903244000⟩, ⟨.privateRow 13 8, 17903229989984798659200⟩, ⟨.privateRow 13 9, 19022181864358848575400⟩, ⟨.privateRow 14 5, 1509006036531899505600⟩, ⟨.privateRow 14 6, 7964198526140580724000⟩, ⟨.privateRow 15 3, 2006978028587426342448⟩, ⟨.hall 5 31, 8874605970160025858012250⟩, ⟨.hall 4 32, 48879037623506501558347200⟩, ⟨.hall 3 33, 144998259688886884340860800⟩, ⟨.hall 2 34, 357173278413296034338288640⟩, ⟨.assumptionRow 18, 165335232058765797600⟩]
  caps := #[0, 33531578574367704355324800, 1853150738724680252457600, 268176478469915108670720, 0, 344967333788857537778592, 0, 0, 0, 0, 9375840057998957958576, 4370500216582041484800, 1522339710547450766400, 45039212437619018018400, 18509981963785405693600, 0, 116657634952277072253600, 19308647508682777845600, 2211725382767045402400, 132058923045878400000] }

theorem case_56_37_18_checked :
    (Witness.linear .conditional case_56_37_18).check 56 37 18 = true := by
  change case_56_37_18.check 56 37 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_37_19 : Certificate := {
  objectiveScale := 34945036574282714880000
  eta := 37057168253070082584997885555200
  rows := #[⟨.count 2, 4864224340854087379432149888000⟩, ⟨.count 3, 625054842805690930033079078400⟩, ⟨.count 4, 77527353568500833439789547200⟩, ⟨.count 5, 9067526733157992215180064000⟩, ⟨.count 6, 1101056817597756197557579200⟩, ⟨.count 7, 174375514099192157984232000⟩, ⟨.count 8, 46500137093117908795795200⟩, ⟨.count 9, 12681855570850338762489600⟩, ⟨.count 10, 6340927785425169381244800⟩, ⟨.path 7, 32083599077137801000061100⟩, ⟨.path 8, 248583500942139483120000⟩, ⟨.privateRow 2 35, 366529580613653063098056364800⟩, ⟨.privateRow 3 31, 10830656931272046257020632000⟩, ⟨.privateRow 3 32, 66965364095989023989144620800⟩, ⟨.privateRow 3 33, 113344084164474902689750800000⟩, ⟨.privateRow 4 28, 2348741299630507705737613800⟩, ⟨.privateRow 4 29, 12482961802647502616231221440⟩, ⟨.privateRow 4 30, 25426856214230536503400762800⟩, ⟨.privateRow 4 31, 40602369705140787363528508800⟩, ⟨.privateRow 4 32, 67307495313004013047263683400⟩, ⟨.privateRow 5 25, 282100831698248646694490880⟩, ⟨.privateRow 5 26, 2141663456974459113680624640⟩, ⟨.privateRow 5 27, 5141623492024031882015065920⟩, ⟨.privateRow 5 28, 8968791442063605188836992192⟩, ⟨.privateRow 5 29, 14170529277985240056278622240⟩, ⟨.privateRow 5 30, 24307688331332425056841964160⟩, ⟨.privateRow 5 31, 28799472407480134163435792160⟩, ⟨.privateRow 6 23, 297453257913119321344531200⟩, ⟨.privateRow 6 24, 975568724415658983865355100⟩, ⟨.privateRow 6 25, 1946125635585950029856673600⟩, ⟨.privateRow 6 26, 3308567790134434064229392400⟩, ⟨.privateRow 6 27, 5098684674954315463853234400⟩, ⟨.privateRow 6 28, 8696909569064629834956434400⟩, ⟨.privateRow 6 29, 11002172317891304575376551200⟩, ⟨.privateRow 6 30, 10715513734660516197145329600⟩, ⟨.privateRow 7 20, 9511391678137754071867200⟩, ⟨.privateRow 7 21, 157104034607462649002936640⟩, ⟨.privateRow 7 22, 405953577797061108534720000⟩, ⟨.privateRow 7 23, 772442009479873833165865800⟩, ⟨.privateRow 7 24, 1287531857165055566503982400⟩, ⟨.privateRow 7 25, 1960202207699172798165604800⟩, ⟨.privateRow 7 26, 3300181158265853869964436480⟩, ⟨.privateRow 7 27, 4260575061156928393414735200⟩, ⟨.privateRow 7 28, 4441316665453392646055534400⟩, ⟨.privateRow 7 29, 2317533618337358633019007200⟩, ⟨.privateRow 8 18, 6296893564693050149430600⟩, ⟨.privateRow 8 19, 73184874856782163275200400⟩, ⟨.privateRow 8 20, 176603645668237391114030520⟩, ⟨.privateRow 8 21, 330237084726124407836804800⟩, ⟨.privateRow 8 22, 543470352275815559050856400⟩, ⟨.privateRow 8 23, 819011343205570786468797600⟩, ⟨.privateRow 8 24, 1368201950441254024776279600⟩, ⟨.privateRow 8 25, 1805367822640302808996748640⟩, ⟨.privateRow 8 26, 1627989174687180119402788200⟩, ⟨.privateRow 9 16, 3034973982767602438886400⟩, ⟨.privateRow 9 17, 33876993816577062342391200⟩, ⟨.privateRow 9 18, 83584957171513596389136000⟩, ⟨.privateRow 9 19, 155845914015116385236816640⟩, ⟨.privateRow 9 20, 255202772598593236825408000⟩, ⟨.privateRow 9 21, 378782366737689632065748400⟩, ⟨.privateRow 9 22, 641641502096594520721200000⟩, ⟨.privateRow 9 23, 836650193910265404469800000⟩, ⟨.privateRow 10 14, 1358770239733964867409600⟩, ⟨.privateRow 10 15, 16388859506945053169986560⟩, ⟨.privateRow 10 16, 43646719589676582574235040⟩, ⟨.privateRow 10 17, 83181443585168358337602240⟩, ⟨.privateRow 10 18, 136773812331620903553450336⟩, ⟨.privateRow 10 19, 205234695988261315639623360⟩, ⟨.privateRow 10 20, 336227695822169606440505520⟩, ⟨.privateRow 11 12, 610607860818720014490240⟩, ⟨.privateRow 11 13, 8504895204260743058971200⟩, ⟨.privateRow 11 14, 25309515177722684624284800⟩, ⟨.privateRow 11 15, 50962271460639324286300800⟩, ⟨.privateRow 11 16, 85698599766655319516217600⟩, ⟨.privateRow 11 17, 102511665864373571663457600⟩, ⟨.privateRow 12 10, 302735267533319718722625⟩, ⟨.privateRow 12 11, 4843764280533115499562000⟩, ⟨.privateRow 12 12, 16468798553812592698510800⟩, ⟨.privateRow 12 13, 36067414027354275412123200⟩, ⟨.privateRow 12 14, 29869879729954212247299000⟩, ⟨.privateRow 13 8, 195378727282008020150400⟩, ⟨.privateRow 13 9, 3113848466057002821147000⟩, ⟨.privateRow 13 10, 12067892721785362044623040⟩, ⟨.privateRow 13 11, 11269165877158676876532000⟩, ⟨.privateRow 14 6, 199901383006128576172400⟩, ⟨.privateRow 14 7, 2328263166777262240125600⟩, ⟨.privateRow 14 8, 5172448285283576908460850⟩, ⟨.privateRow 15 5, 1679171617251480039848160⟩, ⟨.hall 5 31, 5024921064625054019245618800⟩, ⟨.hall 4 32, 18593009361930024441227808000⟩, ⟨.hall 3 33, 48235686327563986038791203200⟩, ⟨.hall 2 34, 109616323174176617001287884800⟩, ⟨.assumptionRow 19, 36487654616817793467936⟩]
  caps := #[0, 149307939496915537535920800, 2325936828731598851483204160, 0, 0, 17260076780322705459566832, 1203277689630389009142000, 6628449093575296072316220, 0, 3732471968858331924733760, 0, 7989458185291973676919200, 1993340567716219776947475, 11229913991761688388847968, 36487654616817793467936, 24035511177781306824260640, 121802972082450109082311680, 26994883460709554246450880, 4654867776188252379337152, 557577967145988359492064] }

theorem case_56_37_19_checked :
    (Witness.linear .conditional case_56_37_19).check 56 37 19 = true := by
  change case_56_37_19.check 56 37 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_37_20 : Certificate := {
  objectiveScale := 5375238282478064000000
  eta := 5403264139330855820337146832000
  rows := #[⟨.count 2, 708078396954363261793975008000⟩, ⟨.count 3, 89950392697451022856383264000⟩, ⟨.count 4, 10849279820964487405923420000⟩, ⟨.count 5, 1273221268245419183174484000⟩, ⟨.count 6, 143461551351596527681632000⟩, ⟨.count 7, 23450445894010970871036000⟩, ⟨.count 8, 6437377304238305729304000⟩, ⟨.count 9, 2257262171616029281704000⟩, ⟨.count 10, 752420723872009760568000⟩, ⟨.path 6, 1528878056664845266380000⟩, ⟨.path 7, 4419988951371836987702250⟩, ⟨.privateRow 2 35, 58532312951451383294105856000⟩, ⟨.privateRow 3 31, 908589825226778008650336000⟩, ⟨.privateRow 3 32, 9970577818935958673873424000⟩, ⟨.privateRow 3 33, 17908783660390966538923728000⟩, ⟨.privateRow 4 28, 135989595552034208531547000⟩, ⟨.privateRow 4 29, 1630081877232515545782543600⟩, ⟨.privateRow 4 30, 3764744929609474503770327250⟩, ⟨.privateRow 4 31, 6419904422983944613753032000⟩, ⟨.privateRow 4 32, 11279664475019276988968316000⟩, ⟨.privateRow 5 26, 228001394112358767208308000⟩, ⟨.privateRow 5 27, 684032646930598443793114800⟩, ⟨.privateRow 5 28, 1310043066425662291946102880⟩, ⟨.privateRow 5 29, 2235908053461028382471435400⟩, ⟨.privateRow 5 30, 4116549515172200363753496000⟩, ⟨.privateRow 5 31, 5294329001337876856984227600⟩, ⟨.privateRow 6 23, 15513203469567481663986000⟩, ⟨.privateRow 6 24, 108716956883631743633736750⟩, ⟨.privateRow 6 25, 253741519397381613586560000⟩, ⟨.privateRow 6 26, 476212649625438473832084000⟩, ⟨.privateRow 6 27, 798858817198919950274802000⟩, ⟨.privateRow 6 28, 1478166341604842794148244000⟩, ⟨.privateRow 6 29, 2059128695391764446922472000⟩, ⟨.privateRow 6 30, 2252260962439499058097050000⟩, ⟨.privateRow 7 21, 9912247298056738107673200⟩, ⟨.privateRow 7 22, 43813578182928060422916000⟩, ⟨.privateRow 7 23, 97595238058898599360341000⟩, ⟨.privateRow 7 24, 181184957711710214316912000⟩, ⟨.privateRow 7 25, 302852327155007230254654000⟩, ⟨.privateRow 7 26, 558435912390321758439847200⟩, ⟨.privateRow 7 27, 800714489738151910854933000⟩, ⟨.privateRow 7 28, 952534778456731340618748000⟩, ⟨.privateRow 7 29, 774061777072899946062432000⟩, ⟨.privateRow 8 19, 4493623767568947181170000⟩, ⟨.privateRow 8 20, 17737273536499474536278700⟩, ⟨.privateRow 8 21, 39875976079031727156522000⟩, ⟨.privateRow 8 22, 73957993269898570510552875⟩, ⟨.privateRow 8 23, 123361169156729981220744000⟩, ⟨.privateRow 8 24, 227626427832307471338871500⟩, ⟨.privateRow 8 25, 335433338817274573537662000⟩, ⟨.privateRow 8 26, 416072984869474064057425500⟩, ⟨.privateRow 8 27, 260828733987798494639121000⟩, ⟨.privateRow 9 17, 1832283799799431176198000⟩, ⟨.privateRow 9 18, 7577408704044381124104000⟩, ⟨.privateRow 9 19, 17589924478074539291500800⟩, ⟨.privateRow 9 20, 33060066126672626393352000⟩, ⟨.privateRow 9 21, 55261122053266494637272000⟩, ⟨.privateRow 9 22, 101994809235983545321440000⟩, ⟨.privateRow 9 23, 155068337703177715284468000⟩, ⟨.privateRow 9 24, 193539330640411399523880000⟩, ⟨.privateRow 10 15, 735057168705732612247200⟩, ⟨.privateRow 10 16, 3454865157112311483941400⟩, ⟨.privateRow 10 17, 8522874744950219651524800⟩, ⟨.privateRow 10 18, 16470489645558293658833520⟩, ⟨.privateRow 10 19, 27889728164855828458387200⟩, ⟨.privateRow 10 20, 51597251139523069330950600⟩, ⟨.privateRow 10 21, 80820734611337734138725600⟩, ⟨.privateRow 10 22, 23224719676849367942865600⟩, ⟨.privateRow 11 13, 304551245376765855468000⟩, ⟨.privateRow 11 14, 1691338892122551854952000⟩, ⟨.privateRow 11 15, 4584192928775763170868000⟩, ⟨.privateRow 11 16, 9310256431749615724200000⟩, ⟨.privateRow 11 17, 16193766023778698958002400⟩, ⟨.privateRow 11 18, 30264033560185281480624000⟩, ⟨.privateRow 11 19, 14630402964177967566600000⟩, ⟨.privateRow 12 11, 137943799376535122770800⟩, ⟨.privateRow 12 12, 903203448298741875285000⟩, ⟨.privateRow 12 13, 2750033436288616870623000⟩, ⟨.privateRow 12 14, 6035041222723411621222500⟩, ⟨.privateRow 12 15, 11004153086628142748307000⟩, ⟨.privateRow 12 16, 5943078689805721539375300⟩, ⟨.privateRow 13 9, 61582053293096036951250⟩, ⟨.privateRow 13 10, 525500188101086181984000⟩, ⟨.privateRow 13 11, 1858018522214554714872000⟩, ⟨.privateRow 13 12, 4502121803827574886036000⟩, ⟨.privateRow 13 13, 1954203824500914239253000⟩, ⟨.privateRow 14 7, 50231635627309708572000⟩, ⟨.privateRow 14 8, 346912233551107674825375⟩, ⟨.privateRow 14 9, 1423229676107108409540000⟩, ⟨.privateRow 14 10, 975928920759160052256000⟩, ⟨.privateRow 15 6, 281297159512934368003200⟩, ⟨.privateRow 15 7, 523036905969362340505950⟩, ⟨.privateRow 16 4, 249065193318743971669500⟩, ⟨.hall 6 30, 152965052737214961255012000⟩, ⟨.hall 5 31, 1245761830682027660297921625⟩, ⟨.hall 4 32, 3701199341877742234998468000⟩, ⟨.hall 3 33, 8656216841111772839378472000⟩, ⟨.hall 2 34, 18279734243171523274786233600⟩, ⟨.assumptionRow 20, 4395533531072314254624⟩]
  caps := #[0, 3349402622456099953144816800, 87915327256378683589318560, 0, 29193186931729288161052590, 0, 1358136238897028866610500, 398096267508777397660650, 1861887142940043658984545, 124120318836350482365216, 26430880008988227143448, 939165641980367746218400, 75677499079127972874848, 276112089006079598217660, 1633870190750363193979923, 7846214539550601364394244, 0, 15739500982062528578107200, 3621319052694503305297152, 650933098106309297671392] }

theorem case_56_37_20_checked :
    (Witness.linear .conditional case_56_37_20).check 56 37 20 = true := by
  change case_56_37_20.check 56 37 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_37_21 : Certificate := {
  objectiveScale := 3714494784000000
  eta := 4357773076501547948044800
  rows := #[⟨.count 2, 570626652029295397536000⟩, ⟨.count 3, 71851487860740222835200⟩, ⟨.count 4, 8475835207966521595200⟩, ⟨.count 5, 898845821557344460800⟩, ⟨.count 6, 81257267350608148800⟩, ⟨.count 7, 5941889445391099200⟩, ⟨.count 8, 720229023683769600⟩, ⟨.count 9, 294639146052451200⟩, ⟨.path 7, 3883930273561060800⟩, ⟨.privateRow 2 35, 48467452034287433347200⟩, ⟨.privateRow 3 31, 639023201263424577600⟩, ⟨.privateRow 3 32, 8008466590681062105600⟩, ⟨.privateRow 3 33, 14718600328001515545600⟩, ⟨.privateRow 4 28, 110600169449438869200⟩, ⟨.privateRow 4 29, 1255224145338869706000⟩, ⟨.privateRow 4 30, 2989715691625307845200⟩, ⟨.privateRow 4 31, 5233319129028210620400⟩, ⟨.privateRow 4 32, 9465092279153169258600⟩, ⟨.privateRow 5 25, 9480014524237617360⟩, ⟨.privateRow 5 26, 172813809739894202880⟩, ⟨.privateRow 5 27, 520659563129527741920⟩, ⟨.privateRow 5 28, 1022905270886873774400⟩, ⟨.privateRow 5 29, 1800617573523404235600⟩, ⟨.privateRow 5 30, 3439957862918420363520⟩, ⟨.privateRow 5 31, 4623438194635590570240⟩, ⟨.privateRow 6 23, 18242943881640878400⟩, ⟨.privateRow 6 24, 80358588725074159500⟩, ⟨.privateRow 6 25, 189337553876622808800⟩, ⟨.privateRow 6 26, 364543062922035597600⟩, ⟨.privateRow 6 27, 633371975674020142560⟩, ⟨.privateRow 6 28, 1223749493942260685400⟩, ⟨.privateRow 6 29, 1799252139332670422400⟩, ⟨.privateRow 6 30, 2095551358721907886800⟩, ⟨.privateRow 7 20, 841826131578432000⟩, ⟨.privateRow 7 21, 9807975954665048160⟩, ⟨.privateRow 7 22, 32015894933752329600⟩, ⟨.privateRow 7 23, 71051879309660449200⟩, ⟨.privateRow 7 24, 135583113708469627200⟩, ⟨.privateRow 7 25, 235450584581763751200⟩, ⟨.privateRow 7 26, 455874105033668280960⟩, ⟨.privateRow 7 27, 694352223761417020800⟩, ⟨.privateRow 7 28, 889328509458666076800⟩, ⟨.privateRow 7 29, 813151428971541660000⟩, ⟨.privateRow 8 18, 517664610772709400⟩, ⟨.privateRow 8 19, 4390941718253890800⟩, ⟨.privateRow 8 20, 12959620994909829240⟩, ⟨.privateRow 8 21, 28379024169317421600⟩, ⟨.privateRow 8 22, 53927148148322248800⟩, ⟨.privateRow 8 23, 93636203695172938800⟩, ⟨.privateRow 8 24, 182112909592706492400⟩, ⟨.privateRow 8 25, 286354056953870745840⟩, ⟨.privateRow 8 26, 383780787416993666700⟩, ⟨.privateRow 8 27, 405383906934675068400⟩, ⟨.privateRow 8 28, 9588048877790182800⟩, ⟨.privateRow 9 16, 231682063562611200⟩, ⟨.privateRow 9 17, 1939707711511970400⟩, ⟨.privateRow 9 18, 5633857610881718400⟩, ⟨.privateRow 9 19, 12345380219597705280⟩, ⟨.privateRow 9 20, 23491106237120121600⟩, ⟨.privateRow 9 21, 40774784045369774400⟩, ⟨.privateRow 9 22, 79435649138109264000⟩, ⟨.privateRow 9 23, 129051945970973625600⟩, ⟨.privateRow 9 24, 181641759773046693120⟩, ⟨.privateRow 9 25, 112658551261444188000⟩, ⟨.privateRow 10 14, 98914570460465760⟩, ⟨.privateRow 10 15, 897516167975159040⟩, ⟨.privateRow 10 16, 2705769491248343520⟩, ⟨.privateRow 10 17, 6005281504087232640⟩, ⟨.privateRow 10 18, 11485033913124547776⟩, ⟨.privateRow 10 19, 19979807870645663040⟩, ⟨.privateRow 10 20, 38859220374992657640⟩, ⟨.privateRow 10 21, 64946886051276028800⟩, ⟨.privateRow 10 22, 83019490052712333120⟩, ⟨.privateRow 11 12, 45832756052603520⟩, ⟨.privateRow 11 13, 451312342762881600⟩, ⟨.privateRow 11 14, 1460604313764288000⟩, ⟨.privateRow 11 15, 3344699935743566400⟩, ⟨.privateRow 11 16, 6479085060163497600⟩, ⟨.privateRow 11 17, 11333785818150956160⟩, ⟨.privateRow 11 18, 21985172823963148800⟩, ⟨.privateRow 11 19, 37546030069878330000⟩, ⟨.privateRow 11 20, 4157685727629033600⟩, ⟨.privateRow 12 10, 25320551613882525⟩, ⟨.privateRow 12 11, 252080158289319360⟩, ⟨.privateRow 12 12, 897070971463266600⟩, ⟨.privateRow 12 13, 2174537629199073600⟩, ⟨.privateRow 12 14, 4321374142102617600⟩, ⟨.privateRow 12 15, 7656525587001891600⟩, ⟨.privateRow 12 16, 14827715025089606640⟩, ⟨.privateRow 12 17, 1760559835671436800⟩, ⟨.privateRow 13 8, 18157034210515200⟩, ⟨.privateRow 13 9, 163980715213715400⟩, ⟨.privateRow 13 10, 637917135262767360⟩, ⟨.privateRow 13 11, 1664610957799732800⟩, ⟨.privateRow 13 12, 3466596839269132800⟩, ⟨.privateRow 13 13, 5337411514799364000⟩, ⟨.privateRow 14 6, 9288667964175600⟩, ⟨.privateRow 14 7, 127855782565711200⟩, ⟨.privateRow 14 8, 543387075904272600⟩, ⟨.privateRow 14 9, 1515910611753457920⟩, ⟨.privateRow 14 10, 1660017660454810800⟩, ⟨.privateRow 15 4, 24639413968128960⟩, ⟨.privateRow 15 5, 130041351498458400⟩, ⟨.privateRow 15 6, 550763371052294400⟩, ⟨.privateRow 15 7, 555926777655909660⟩, ⟨.privateRow 16 3, 184795604760967200⟩, ⟨.privateRow 16 4, 195062027247687600⟩, ⟨.hall 6 30, 250794035032741200000⟩, ⟨.hall 5 31, 1250908397986014617850⟩, ⟨.hall 4 32, 3379609218270299414400⟩, ⟨.hall 3 33, 7530312190712495184000⟩, ⟨.hall 2 34, 15421358653367927420160⟩, ⟨.assumptionRow 21, 1846948336128896⟩]
  caps := #[0, 0, 0, 8383034417387044800, 2172676318480649520, 913558093315678272, 1957980960198844680, 0, 0, 729923731467168000, 124652607108669864, 17521411597714024, 448174241329112375, 0, 1559634806505118200, 0, 0, 32749856317298440320, 9324171564857140992, 2213372016414599040] }

theorem case_56_37_21_checked :
    (Witness.linear .conditional case_56_37_21).check 56 37 21 = true := by
  change case_56_37_21.check 56 37 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_37_22 : Certificate := {
  objectiveScale := 160282173803413662000000
  eta := 277373829261956350263915121747200
  rows := #[⟨.count 2, 37334634571104717146782395513600⟩, ⟨.count 3, 4851126802239525835121334240000⟩, ⟨.count 4, 595283130031822188926571201600⟩, ⟨.count 5, 67250823270921775595918808000⟩, ⟨.count 6, 6541572857492551526665617600⟩, ⟨.count 7, 488251439477738042355849600⟩, ⟨.count 8, 23250068546558954397897600⟩, ⟨.path 7, 175554235830680651488005000⟩, ⟨.path 8, 18976154223348807742857600⟩, ⟨.privateRow 2 35, 3386116733052299559555408566400⟩, ⟨.privateRow 3 34, 5980940633191011665132770214400⟩, ⟨.privateRow 4 29, 79703559984458751571432762560⟩, ⟨.privateRow 4 32, 1613396366039218002337257762600⟩, ⟨.privateRow 5 26, 9602942597401606993600220160⟩, ⟨.privateRow 5 27, 33277823110689831429710834880⟩, ⟨.privateRow 5 28, 53631398117718471288718351872⟩, ⟨.privateRow 5 29, 93546650797079953019940993600⟩, ⟨.privateRow 5 30, 158016765869833277669871248640⟩, ⟨.privateRow 5 31, 404562817744399086000617188800⟩, ⟨.privateRow 6 23, 1019497053331255738479240000⟩, ⟨.privateRow 6 24, 4819822245660766100092736400⟩, ⟨.privateRow 6 25, 11931199716742072409668053600⟩, ⟨.privateRow 6 27, 83341365352404279400618097760⟩, ⟨.privateRow 6 28, 50370650736426763302480921000⟩, ⟨.privateRow 6 29, 98310700556882009247281630400⟩, ⟨.privateRow 6 30, 121812506452763527562142181200⟩, ⟨.privateRow 7 20, 88772988995952371337427200⟩, ⟨.privateRow 7 21, 598855336992082782562991040⟩, ⟨.privateRow 7 22, 1953005757910952169423398400⟩, ⟨.privateRow 7 23, 4408586658243504594179922600⟩, ⟨.privateRow 7 25, 21376777309379061500695564800⟩, ⟨.privateRow 7 26, 39289294405320838796104387200⟩, ⟨.privateRow 7 28, 127103142586492112488792344000⟩, ⟨.privateRow 7 29, 14131889878353101603493544800⟩, ⟨.privateRow 8 17, 5588958785230517884110000⟩, ⟨.privateRow 8 18, 59578300650557320644612600⟩, ⟨.privateRow 8 19, 280586054505063745120082400⟩, ⟨.privateRow 8 20, 795152344292316240408097920⟩, ⟨.privateRow 8 21, 1740848882423601710542582800⟩, ⟨.privateRow 8 22, 2635249956824041487536706100⟩, ⟨.privateRow 8 23, 2377734688681127354227849200⟩, ⟨.privateRow 8 24, 15083481969580121665636068000⟩, ⟨.privateRow 8 25, 23652875984128088282841175920⟩, ⟨.privateRow 8 26, 13772032790625780644129656500⟩, ⟨.privateRow 8 27, 43835097985968588647936187600⟩, ⟨.privateRow 8 28, 37053343616794173636999431400⟩, ⟨.privateRow 9 14, 140909506342781541805440⟩, ⟨.privateRow 9 15, 4227285190283446254163200⟩, ⟨.privateRow 9 16, 32680166278729719118723200⟩, ⟨.privateRow 9 17, 131221977781715310806316000⟩, ⟨.privateRow 9 19, 1449113363229165375927144960⟩, ⟨.privateRow 9 20, 1020889373453452270380412800⟩, ⟨.privateRow 9 21, 2143233591473707250860742400⟩, ⟨.privateRow 9 22, 2831073281721256577073868800⟩, ⟨.privateRow 9 23, 10401587484458276462223067200⟩, ⟨.privateRow 9 24, 15153549221609069787298823040⟩, ⟨.privateRow 9 25, 12339445470437379615902380800⟩, ⟨.privateRow 9 26, 6337405047766599842699664000⟩, ⟨.privateRow 10 12, 118892395976721925898340⟩, ⟨.privateRow 10 13, 2790008225587074527747712⟩, ⟨.privateRow 10 14, 18207521212435129223288640⟩, ⟨.privateRow 10 15, 66726070849704859334945280⟩, ⟨.privateRow 10 16, 67055311330871166206663760⟩, ⟨.privateRow 10 17, 330650561610897923371092480⟩, ⟨.privateRow 10 18, 1070602247291185598329372032⟩, ⟨.privateRow 10 19, 927043642229159763537989760⟩, ⟨.privateRow 10 20, 2118424711513231275656622120⟩, ⟨.privateRow 10 21, 2654765294392220557944876480⟩, ⟨.privateRow 10 22, 7466442467338136946415752000⟩, ⟨.privateRow 10 23, 10599494886116713137688807680⟩, ⟨.privateRow 11 10, 124331917361277831004800⟩, ⟨.privateRow 11 11, 1849437270749007736196400⟩, ⟨.privateRow 11 12, 11272760507422523344435200⟩, ⟨.privateRow 11 13, 38649464596877222895206400⟩, ⟨.privateRow 11 14, 63084102070383736408281600⟩, ⟨.privateRow 11 15, 129460608952430541533748000⟩, ⟨.privateRow 11 16, 404666482306224445966713600⟩, ⟨.privateRow 11 17, 1013914352889484584061043520⟩, ⟨.privateRow 11 18, 1044139442000011224778310400⟩, ⟨.privateRow 11 20, 6664617051424016122992153600⟩, ⟨.privateRow 12 8, 161458809351103849985400⟩, ⟨.privateRow 12 9, 1367651090974056141052800⟩, ⟨.privateRow 12 10, 7992211062879640574277300⟩, ⟨.privateRow 12 11, 26543828257321472937599760⟩, ⟨.privateRow 12 12, 53558193616180448523728400⟩, ⟨.privateRow 12 13, 90764690672143610437946400⟩, ⟨.privateRow 12 14, 188664618726764848707939900⟩, ⟨.privateRow 12 15, 475569583906887703593360000⟩, ⟨.privateRow 12 16, 1308397607457605158741687440⟩, ⟨.privateRow 12 17, 1247107843427926137287229600⟩, ⟨.privateRow 12 18, 240129614207429200890786150⟩, ⟨.privateRow 12 19, 3678908167697480266424475600⟩, ⟨.privateRow 13 7, 1383932651580890142732000⟩, ⟨.privateRow 13 8, 6740566091229276695188800⟩, ⟨.privateRow 13 9, 22108324109004720030143700⟩, ⟨.privateRow 13 10, 49821575456912045138352000⟩, ⟨.privateRow 13 11, 87899493841837679636949600⟩, ⟨.privateRow 13 12, 146015540377565301520862400⟩, ⟨.privateRow 13 13, 275679384194913316432214400⟩, ⟨.privateRow 13 14, 760458410837775670793572800⟩, ⟨.privateRow 13 15, 1892223435853519474354608960⟩, ⟨.privateRow 13 16, 1822916088662348496006590400⟩, ⟨.privateRow 13 17, 663249723270141600904311000⟩, ⟨.privateRow 13 20, 3021180335707146417189665280⟩, ⟨.privateRow 14 5, 1136281545508520327716800⟩, ⟨.privateRow 14 6, 6596745639202243013689200⟩, ⟨.privateRow 14 7, 22224330228328412292108000⟩, ⟨.privateRow 14 8, 53973373411654715566548000⟩, ⟨.privateRow 14 9, 103628876950377053887772160⟩, ⟨.privateRow 14 10, 171172698534104955082480800⟩, ⟨.privateRow 14 11, 267375788285427975575822400⟩, ⟨.privateRow 14 12, 548729296351822941593238000⟩, ⟨.privateRow 14 13, 1384662361524450975716349600⟩, ⟨.privateRow 14 14, 3255673884191012442974175360⟩, ⟨.privateRow 14 15, 3304369861091305364129772000⟩, ⟨.privateRow 15 3, 1511254455526332035863344⟩, ⟨.privateRow 15 4, 9544764982271570752821120⟩, ⟨.privateRow 15 5, 28545917493275160677418720⟩, ⟨.privateRow 15 6, 72895803148917192318114240⟩, ⟨.privateRow 15 7, 149236377483225288541505220⟩, ⟨.privateRow 15 8, 263965778231932662264130752⟩, ⟨.privateRow 15 9, 410197637928575838305764800⟩, ⟨.privateRow 15 10, 697502056396768631936928000⟩, ⟨.privateRow 15 13, 169260499018949188016694528⟩, ⟨.privateRow 15 15, 30379992692218089750942872760⟩, ⟨.privateRow 16 1, 5397337341165471556654800⟩, ⟨.privateRow 16 2, 11334408416447490268975080⟩, ⟨.privateRow 16 3, 47723824911357853764105600⟩, ⟨.privateRow 16 4, 125937871293861002988612000⟩, ⟨.privateRow 16 5, 273359261808439471192928400⟩, ⟨.privateRow 16 6, 517132384000416743521988025⟩, ⟨.privateRow 16 7, 853858767372377600262789360⟩, ⟨.privateRow 16 9, 4307075198250046302210530400⟩, ⟨.privateRow 16 13, 163719232682019303885195600⟩, ⟨.privateRow 16 14, 28336021041118725672437700⟩, ⟨.privateRow 16 17, 1813505346631598443036012800⟩, ⟨.privateRow 16 21, 795108750413791442368601862000⟩, ⟨.privateRow 17 1, 211575623773686485020868160⟩, ⟨.privateRow 17 2, 254527066193908553408563200⟩, ⟨.privateRow 17 3, 705252079245621616736227200⟩, ⟨.privateRow 17 4, 1351239277882367467360166400⟩, ⟨.privateRow 17 5, 2418007128842131257381350400⟩, ⟨.privateRow 17 6, 4271812594287765221373719040⟩, ⟨.privateRow 17 8, 18693055111433399335909670400⟩, ⟨.privateRow 17 9, 2871383465500030868140353600⟩, ⟨.privateRow 17 12, 470168052830414411157484800⟩, ⟨.privateRow 17 13, 377813613881583008965836000⟩, ⟨.privateRow 18 1, 6760875195775695949914960000⟩, ⟨.privateRow 18 2, 3140050924260267674516059200⟩, ⟨.privateRow 18 3, 10276530297579057843870739200⟩, ⟨.privateRow 18 10, 10790356812458010736064276160⟩, ⟨.privateRow 18 14, 548937993395681339826761985600⟩, ⟨.privateRow 19 3, 450882766806281162899828682400⟩, ⟨.privateRow 19 10, 71935712083053404907095174400⟩, ⟨.hall 13 9, 21126950672491161347850⟩, ⟨.hall 10 14, 1437314478182752449280⟩, ⟨.hall 18 15, 12909294638522299443190564800⟩, ⟨.hall 11 19, 14127978932648211441888⟩, ⟨.hall 16 19, 2154617066593256245416596160⟩, ⟨.hall 17 19, 2055306059515811568774147840⟩, ⟨.hall 14 20, 6115560096709229958792000⟩, ⟨.hall 6 21, 5568319927272472834464⟩, ⟨.hall 5 24, 80081055062918460144594⟩, ⟨.hall 4 28, 10124824129311185479425240⟩, ⟨.hall 3 30, 74259242997529011629407200⟩]
  caps := #[0, 0, 7842328381242732540950740800, 392546517896765194062408000, 29594295820377290848479480, 15978639914104270523233344, 0, 0, 0, 8448622862257151224801920, 3612987345998795938213572, 27299137381569450884586400, 2180513381093872964711880, 0, 167392279212445964797048500, 12521822631503894011439136, 2598465896830414013610282075, 0, 18835807087442595946380484800, 0] }

theorem case_56_37_22_checked :
    (Witness.linear .conditional case_56_37_22).check 56 37 22 = true := by
  change case_56_37_22.check 56 37 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_37_23 : Certificate := {
  objectiveScale := 579633989907772800000
  eta := 1040899631986643766246849139200
  rows := #[⟨.count 2, 127849746530068345547033068800⟩, ⟨.count 3, 14747847478944123045671769600⟩, ⟨.count 4, 1549384754597242498961625600⟩, ⟨.count 5, 140273516877116604844262400⟩, ⟨.count 6, 9905678545705474530398400⟩, ⟨.count 7, 367850131670760327388800⟩, ⟨.path 6, 2390072169742724290824000⟩, ⟨.path 7, 392474122789883553480600⟩, ⟨.privateRow 2 35, 13142672121043481897056176000⟩, ⟨.privateRow 4 29, 213279506342706837820026240⟩, ⟨.privateRow 4 31, 2164476156017212611396622800⟩, ⟨.privateRow 5 26, 22316241321359459861587200⟩, ⟨.privateRow 5 27, 87963184541691870954422880⟩, ⟨.privateRow 5 28, 158254031313183369647026944⟩, ⟨.privateRow 5 31, 4326242482731117288381481440⟩, ⟨.privateRow 6 23, 1973545150868523661228800⟩, ⟨.privateRow 6 24, 10724035609467061865883900⟩, ⟨.privateRow 6 25, 30253796543533961619936000⟩, ⟨.privateRow 6 26, 63646831115509888074628800⟩, ⟨.privateRow 6 29, 1124711995642562777667016800⟩, ⟨.privateRow 7 19, 4379168234175718183200⟩, ⟨.privateRow 7 20, 128986409806630244668800⟩, ⟨.privateRow 7 22, 6300163366234133226230400⟩, ⟨.privateRow 7 23, 9498415899927132739360800⟩, ⟨.privateRow 7 24, 22806708163587140298105600⟩, ⟨.privateRow 7 25, 45087916139073194414227200⟩, ⟨.privateRow 7 26, 54625744553107908617236800⟩, ⟨.privateRow 7 27, 106847325745653347951896800⟩, ⟨.privateRow 7 29, 1269477079405198944127848000⟩, ⟨.privateRow 8 16, 1094792058543929545800⟩, ⟨.privateRow 8 17, 8253047825946545806800⟩, ⟨.privateRow 8 18, 80467216302978821616300⟩, ⟨.privateRow 8 19, 119829967135171924831200⟩, ⟨.privateRow 8 20, 1949605697855029735160640⟩, ⟨.privateRow 8 21, 4281366810279127143775200⟩, ⟨.privateRow 8 22, 8062048719117497175271200⟩, ⟨.privateRow 8 23, 16710905981614540587091200⟩, ⟨.privateRow 8 24, 38333049137857149116641200⟩, ⟨.privateRow 8 25, 54337595283299146360782240⟩, ⟨.privateRow 8 27, 307916105356459085713827600⟩, ⟨.privateRow 8 28, 263733217319115539724128400⟩, ⟨.privateRow 8 29, 744727918656273897812266800⟩, ⟨.privateRow 9 14, 743131579132849146240⟩, ⟨.privateRow 9 15, 4777274437282601654400⟩, ⟨.privateRow 9 16, 42015516204818778652800⟩, ⟨.privateRow 9 17, 80815559230697344653600⟩, ⟨.privateRow 9 18, 653618002555483226352000⟩, ⟨.privateRow 9 19, 1777942303075341582379200⟩, ⟨.privateRow 9 20, 3496434079820055233059200⟩, ⟨.privateRow 9 21, 6440164047660053913602400⟩, ⟨.privateRow 9 23, 60730570475684264353598400⟩, ⟨.privateRow 9 24, 30179316560164136677952640⟩, ⟨.privateRow 9 26, 199252154654995177335600000⟩, ⟨.privateRow 9 28, 509583902100872980805424000⟩, ⟨.privateRow 10 12, 627017269893341467140⟩, ⟨.privateRow 10 13, 3344092106097821158080⟩, ⟨.privateRow 10 14, 22930917298956487941120⟩, ⟨.privateRow 10 15, 49389668028521666334720⟩, ⟨.privateRow 10 16, 249134861904287676276960⟩, ⟨.privateRow 10 17, 755156799231544341515520⟩, ⟨.privateRow 10 18, 1637267495145493238995968⟩, ⟨.privateRow 10 19, 3026403356018528148062400⟩, ⟨.privateRow 10 20, 6499661019714377648373240⟩, ⟨.privateRow 10 21, 2809037369122169772787200⟩, ⟨.privateRow 10 22, 41680764010403242914309120⟩, ⟨.privateRow 10 24, 92881322223840458210382480⟩, ⟨.privateRow 10 25, 35948990140551577449360000⟩, ⟨.privateRow 10 27, 194234901798479746324760640⟩, ⟨.privateRow 11 11, 2090057566311138223800⟩, ⟨.privateRow 11 12, 13376368424391284632320⟩, ⟨.privateRow 11 13, 32644708654764444638400⟩, ⟨.privateRow 11 14, 114899574927463598764800⟩, ⟨.privateRow 11 15, 351129671140271221598400⟩, ⟨.privateRow 11 16, 827916136570278753379200⟩, ⟨.privateRow 11 17, 1619655276720044714230080⟩, ⟨.privateRow 11 18, 3425836579802434564166400⟩, ⟨.privateRow 11 19, 6632449343760678630192000⟩, ⟨.privateRow 11 21, 40173693167921824845734400⟩, ⟨.privateRow 11 23, 71365712287549251697725600⟩, ⟨.privateRow 11 24, 50432624617850807309577600⟩, ⟨.privateRow 12 9, 1803186919954707487200⟩, ⟨.privateRow 12 10, 9579430512259383525750⟩, ⟨.privateRow 12 11, 24523342111384021825920⟩, ⟨.privateRow 12 12, 67877107629723631839600⟩, ⟨.privateRow 12 13, 192178113661326709501200⟩, ⟨.privateRow 12 14, 470030723801527084996800⟩, ⟨.privateRow 12 15, 978146941033612688738400⟩, ⟨.privateRow 12 16, 2142727016982178907039760⟩, ⟨.privateRow 12 17, 4117877862869900331602400⟩, ⟨.privateRow 12 18, 7573497762992268615457950⟩, ⟨.privateRow 12 20, 36391617887372580722089200⟩, ⟨.privateRow 12 21, 18781814639556237715926480⟩, ⟨.privateRow 12 22, 35685294544268655510123900⟩, ⟨.privateRow 13 7, 1459722744725239394400⟩, ⟨.privateRow 13 8, 7727943942663032088000⟩, ⟨.privateRow 13 9, 22990633229422520461800⟩, ⟨.privateRow 13 10, 54301686103778905471680⟩, ⟨.privateRow 13 11, 133251833411346853288800⟩, ⟨.privateRow 13 12, 317321267430271271428800⟩, ⟨.privateRow 13 13, 683150244531412036579200⟩, ⟨.privateRow 13 14, 1571723289865975944297600⟩, ⟨.privateRow 13 15, 3145118625785000799174240⟩, ⟨.privateRow 13 16, 5765904841664695607880000⟩, ⟨.privateRow 13 17, 10115878620945909003192000⟩, ⟨.privateRow 13 19, 38891393087714553184999200⟩, ⟨.privateRow 13 21, 33710837066684678574273600⟩, ⟨.privateRow 13 23, 112509590272442551562774400⟩, ⟨.privateRow 14 5, 2996273002330754546400⟩, ⟨.privateRow 14 6, 9488197840714056063600⟩, ⟨.privateRow 14 7, 23441429959411197333600⟩, ⟨.privateRow 14 8, 56929187044284336381600⟩, ⟨.privateRow 14 9, 125244211497425540039520⟩, ⟨.privateRow 14 11, 1138583740885686727632000⟩, ⟨.privateRow 14 12, 1100630949522830503377600⟩, ⟨.privateRow 14 13, 2908563919898890640587200⟩, ⟨.privateRow 14 14, 5556288655522151230844160⟩, ⟨.privateRow 14 15, 9785494706389763153592800⟩, ⟨.privateRow 14 16, 16473883500939779840425500⟩, ⟨.privateRow 14 17, 6709511330219225359260000⟩, ⟨.privateRow 14 18, 38161531715351933487799200⟩, ⟨.privateRow 14 19, 35785686976037133849473760⟩, ⟨.privateRow 14 20, 12481724259459340751665800⟩, ⟨.privateRow 15 4, 8389564406526112729920⟩, ⟨.privateRow 15 5, 35422605271999142637440⟩, ⟨.privateRow 15 6, 75012575870115831467520⟩, ⟨.privateRow 15 7, 169364331456745900735260⟩, ⟨.privateRow 15 9, 546520195625129629263360⟩, ⟨.privateRow 15 10, 2685305961196550389938240⟩, ⟨.privateRow 15 11, 2656695395399935697808000⟩, ⟨.privateRow 15 12, 6636908133235475725069440⟩, ⟨.privateRow 15 13, 12305813071492502152246656⟩, ⟨.privateRow 15 15, 76253799586466654366334120⟩, ⟨.privateRow 15 17, 63920091213322452889260480⟩, ⟨.privateRow 15 20, 98297729629797620818896000⟩, ⟨.privateRow 16 2, 29887823198249276600340⟩, ⟨.privateRow 16 3, 62921733048945845474400⟩, ⟨.privateRow 16 4, 132834769769996784890400⟩, ⟨.privateRow 16 5, 281297159512934368003200⟩, ⟨.privateRow 16 6, 485677126971550744755525⟩, ⟨.privateRow 16 8, 1835966282178169848306600⟩, ⟨.privateRow 16 9, 8460553028427487529942400⟩, ⟨.privateRow 16 10, 7820647070208560710422300⟩, ⟨.privateRow 16 13, 118023692940642143375120400⟩, ⟨.privateRow 16 14, 69265030261942698521287950⟩, ⟨.privateRow 16 15, 84454448980195813022103600⟩, ⟨.privateRow 17 1, 318803447447992283736960⟩, ⟨.privateRow 17 2, 335582576261044509196800⟩, ⟨.privateRow 17 3, 708452105439982852748800⟩, ⟨.privateRow 17 4, 1500251517402316629350400⟩, ⟨.privateRow 17 5, 2391025855859942128027200⟩, ⟨.privateRow 17 8, 1716633947796881527814400⟩, ⟨.privateRow 17 10, 11303031318610635514310400⟩, ⟨.privateRow 17 12, 3188034474479922837369600⟩, ⟨.privateRow 17 13, 2789530165169932482698400⟩, ⟨.privateRow 17 14, 10930403912502592585267200⟩, ⟨.privateRow 17 16, 3967827706937711963390204160⟩, ⟨.privateRow 18 2, 19570989412779526307185600⟩, ⟨.privateRow 18 3, 3188034474479922837369600⟩, ⟨.privateRow 18 5, 27098293033079344117641600⟩, ⟨.privateRow 18 9, 56660067250984083155068800⟩, ⟨.privateRow 18 10, 18968805123155540882349120⟩, ⟨.privateRow 18 13, 15484738876045339495795200⟩, ⟨.privateRow 18 15, 9852939346827649521174485760⟩, ⟨.privateRow 19 5, 1463307823786284582352646400⟩, ⟨.privateRow 19 9, 536546202054971013529303680⟩, ⟨.privateRow 19 10, 162589758198476064705849600⟩, ⟨.privateRow 19 12, 69681324942204027731078400⟩, ⟨.privateRow 19 16, 220634301875332019805837907200⟩, ⟨.hall 17 6, 69213906353840430021840⟩, ⟨.hall 18 6, 1204501746936963327652800⟩, ⟨.hall 15 8, 9961673066483434656360⟩, ⟨.hall 18 11, 787328351997065963884800⟩, ⟨.hall 13 15, 308352787178946810300⟩, ⟨.hall 16 15, 42887829249048055272000⟩, ⟨.hall 14 17, 8369036580950197152000⟩, ⟨.hall 15 21, 19019523853431357836580000⟩, ⟨.hall 6 27, 100670487727030820295840⟩, ⟨.hall 9 27, 4614847106414993198150400⟩, ⟨.hall 4 31, 29213082947258497477089900⟩, ⟨.hall 5 31, 1616084413368002134574717700⟩, ⟨.hall 3 33, 4781770414560371321686396800⟩, ⟨.hall 2 34, 10783572153277974424871777280⟩]
  caps := #[0, 113812958621096674288272000, 16987317330447442034317800, 2683140464008616150939400, 3134794210905899343075120, 164393951886427375491456, 0, 372774286803884868163800, 0, 225912551687063428400640, 0, 39413430168625842423360, 12933814820582517982890, 147280465074480315985440, 0, 6797373127714014364422904, 8569869508472719996438890, 0, 15422978760835823837179520, 0] }

theorem case_56_37_23_checked :
    (Witness.linear .conditional case_56_37_23).check 56 37 23 = true := by
  change case_56_37_23.check 56 37 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_37_24 : Certificate := {
  objectiveScale := 114850334857440124800000
  eta := 176362248846194376718888002067200
  rows := #[⟨.count 2, 19548329217960975735649003257600⟩, ⟨.count 3, 1977244485348243983119324876800⟩, ⟨.count 4, 173323073265431344918563700800⟩, ⟨.count 5, 12043597235966528498873006400⟩, ⟨.count 6, 523634662433327326037956800⟩, ⟨.path 4, 850219399423228626835243200⟩, ⟨.path 5, 1128778202837673608681260800⟩, ⟨.path 6, 481758781869350703364046400⟩, ⟨.path 7, 1948301957992795689576600⟩, ⟨.privateRow 2 35, 2219512789167396759299552889600⟩, ⟨.privateRow 3 34, 3631930018637558333399268364800⟩, ⟨.privateRow 4 29, 26312641787274698133407329200⟩, ⟨.privateRow 5 25, 30545355308610760685547480⟩, ⟨.privateRow 5 26, 2289031524351402310965925440⟩, ⟨.privateRow 5 27, 10391238967843584492264342720⟩, ⟨.privateRow 5 28, 20505533380889098087646388288⟩, ⟨.privateRow 5 31, 472527919379834579016652216320⟩, ⟨.privateRow 6 22, 9973993570158615734056320⟩, ⟨.privateRow 6 23, 164847949284566010048986400⟩, ⟨.privateRow 6 25, 5467885760783383982777304000⟩, ⟨.privateRow 6 26, 6836341426212884534384436000⟩, ⟨.privateRow 7 19, 959037843284482282120800⟩, ⟨.privateRow 7 20, 10985342568531342504292800⟩, ⟨.privateRow 7 21, 83436292365749958544509600⟩, ⟨.privateRow 7 22, 139380166557344758334889600⟩, ⟨.privateRow 7 23, 1268087788282906697534227800⟩, ⟨.privateRow 7 24, 3062070828201168429342840000⟩, ⟨.privateRow 7 25, 5543238734184307590658224000⟩, ⟨.privateRow 7 26, 8493239140127375090461804800⟩, ⟨.privateRow 8 17, 774607488806697227866800⟩, ⟨.privateRow 8 18, 5594387419159479979038000⟩, ⟨.privateRow 8 19, 35092066538364010777602000⟩, ⟨.privateRow 8 20, 76531219894101686113239840⟩, ⟨.privateRow 8 21, 348343856632996953361432800⟩, ⟨.privateRow 8 22, 1002374365827899825244133650⟩, ⟨.privateRow 8 23, 2193799066513253220351330000⟩, ⟨.privateRow 8 24, 5117745611047092284823962400⟩, ⟨.privateRow 8 25, 9013900785246520521425187120⟩, ⟨.privateRow 8 26, 12439679865243019681388896800⟩, ⟨.privateRow 9 15, 348741033921629920771200⟩, ⟨.privateRow 9 16, 2816754504751626283152000⟩, ⟨.privateRow 9 17, 14850555694496074126173600⟩, ⟨.privateRow 9 18, 36173956336779976327267200⟩, ⟨.privateRow 9 19, 114491681436471102989184960⟩, ⟨.privateRow 9 20, 330102763108707255005539200⟩, ⟨.privateRow 9 21, 787893180887442398502333600⟩, ⟨.privateRow 9 22, 2032114004661337548333782400⟩, ⟨.privateRow 9 23, 4285911059885524516304457600⟩, ⟨.privateRow 9 24, 7681439761364604960890605440⟩, ⟨.privateRow 9 25, 11812294745218007453921508000⟩, ⟨.privateRow 9 26, 11602962939606549093978595200⟩, ⟨.privateRow 10 13, 292942468494169133447808⟩, ⟨.privateRow 10 14, 1412401187382601179123360⟩, ⟨.privateRow 10 15, 6929216081689000656553920⟩, ⟨.privateRow 10 16, 17759637152459003715273360⟩, ⟨.privateRow 10 17, 46138438787831638518029760⟩, ⟨.privateRow 10 18, 121278181956586021247392512⟩, ⟨.privateRow 10 19, 294407180836639979115047040⟩, ⟨.privateRow 10 20, 808521213043906808315950080⟩, ⟨.privateRow 10 21, 1869391438233505027301940480⟩, ⟨.privateRow 10 22, 3789210829972077741147396480⟩, ⟨.privateRow 10 24, 24718119313452373768909229280⟩, ⟨.privateRow 10 26, 34634588050065616647534339840⟩, ⟨.privateRow 11 11, 152574202340713090337400⟩, ⟨.privateRow 11 12, 976474894980563778159360⟩, ⟨.privateRow 11 13, 3836151373137929128483200⟩, ⟨.privateRow 11 14, 9952532583455746200470400⟩, ⟨.privateRow 11 15, 23191278755788389731284800⟩, ⟨.privateRow 11 16, 53706119223931007798764800⟩, ⟨.privateRow 11 17, 124012311662531599826238720⟩, ⟨.privateRow 11 18, 342851185348731282109286400⟩, ⟨.privateRow 11 19, 846176526181594799011220400⟩, ⟨.privateRow 11 20, 1840655177038362721830393600⟩, ⟨.privateRow 11 21, 3559657856743730206298433600⟩, ⟨.privateRow 11 23, 17724239937515958278315083200⟩, ⟨.privateRow 12 9, 197448967735040469848400⟩, ⟨.privateRow 12 10, 629368584655441497641775⟩, ⟨.privateRow 12 11, 2461530464430171190776720⟩, ⟨.privateRow 12 12, 6473505442170255404315400⟩, ⟨.privateRow 12 13, 14717542287327247329469200⟩, ⟨.privateRow 12 14, 30769130805377139884709000⟩, ⟨.privateRow 12 15, 64386313387780924122382800⟩, ⟨.privateRow 12 16, 167831622574784399371140000⟩, ⟨.privateRow 12 17, 422562729727179387750003600⟩, ⟨.privateRow 12 18, 978038780554556087335318350⟩, ⟨.privateRow 12 20, 7746548259310131926973918600⟩, ⟨.privateRow 12 21, 370572222645123953811477120⟩, ⟨.privateRow 12 22, 9706541891612655737629881900⟩, ⟨.privateRow 12 25, 39427004775268351100268208800⟩, ⟨.privateRow 13 8, 676967889377281610908800⟩, ⟨.privateRow 13 9, 1798195956158404278976500⟩, ⟨.privateRow 13 10, 4986996785079307867028160⟩, ⟨.privateRow 13 11, 11097437900863294978826400⟩, ⟨.privateRow 13 13, 77682065306043064851784800⟩, ⟨.privateRow 13 14, 62250274555010940857659200⟩, ⟨.privateRow 13 15, 199671678971829211137550560⟩, ⟨.privateRow 13 16, 485273148701948034753124800⟩, ⟨.privateRow 13 17, 1080356130459969290809081200⟩, ⟨.privateRow 13 18, 124126898002248706800206400⟩, ⟨.privateRow 13 19, 6096603569759453867441925600⟩, ⟨.privateRow 13 20, 4795572831559725203516848320⟩, ⟨.privateRow 13 21, 4010696260615704903829185600⟩, ⟨.privateRow 14 6, 692638442372126092642800⟩, ⟨.privateRow 14 7, 2200145640476165235453600⟩, ⟨.privateRow 14 8, 5454527733680492979562050⟩, ⟨.privateRow 14 9, 11636325831851718356399040⟩, ⟨.privateRow 14 10, 17810702803854670953672000⟩, ⟨.privateRow 14 12, 156882607197286559983594200⟩, ⟨.privateRow 14 13, 123541511266737399433197600⟩, ⟨.privateRow 14 14, 372778009684678263060354960⟩, ⟨.privateRow 14 15, 871339160504134624544642400⟩, ⟨.privateRow 14 16, 1856097865946704896759543300⟩, ⟨.privateRow 14 17, 1209346720381732157754328800⟩, ⟨.privateRow 14 18, 6803094780979022481937581600⟩, ⟨.privateRow 14 19, 10998821409492413500730606880⟩, ⟨.privateRow 14 20, 9300749004172909172007518400⟩, ⟨.privateRow 15 5, 1939387638641953059399840⟩, ⟨.privateRow 15 6, 6160407793333262659270080⟩, ⟨.privateRow 15 7, 15272677654305380342773740⟩, ⟨.privateRow 15 8, 27927181996444124055357696⟩, ⟨.privateRow 15 10, 88615096719486162867961920⟩, ⟨.privateRow 15 12, 996492630327665335611626880⟩, ⟨.privateRow 15 13, 495707480436883201982599104⟩, ⟨.privateRow 15 14, 1877327234205410561499045120⟩, ⟨.privateRow 15 15, 3835623902324122663228033560⟩, ⟨.privateRow 15 17, 17919941781051646268854521600⟩, ⟨.privateRow 15 18, 17719796976743796713124458112⟩, ⟨.privateRow 15 22, 215702571945035303172569004480⟩, ⟨.privateRow 16 3, 6889929768859570079446800⟩, ⟨.privateRow 16 4, 14545407289814647945498800⟩, ⟨.privateRow 16 5, 23101529224999734972262800⟩, ⟨.privateRow 16 6, 49090749603124436816058450⟩, ⟨.privateRow 16 7, 95999688112776676440292080⟩, ⟨.privateRow 16 10, 599998050704854227751825500⟩, ⟨.privateRow 16 11, 2451562283210577935541343200⟩, ⟨.privateRow 16 12, 1989811717246643838944235840⟩, ⟨.privateRow 16 16, 87425170515430941476420537400⟩, ⟨.privateRow 16 19, 94428784125476694462178209600⟩, ⟨.privateRow 17 2, 36746292100584373757049600⟩, ⟨.privateRow 17 4, 246416311733330506370803200⟩, ⟨.privateRow 17 5, 174544887477775775345985600⟩, ⟨.privateRow 17 6, 465453033274068734255961600⟩, ⟨.privateRow 17 9, 2385446795529602263061803200⟩, ⟨.privateRow 17 10, 9584101094234233482634118400⟩, ⟨.privateRow 17 13, 24785374021844160099129955200⟩, ⟨.privateRow 17 16, 39796234344932876778884716800⟩, ⟨.privateRow 17 17, 707081339172469665926587665600⟩, ⟨.privateRow 17 19, 149061333906020512145471702400⟩, ⟨.privateRow 18 6, 14412420708879199735711382400⟩, ⟨.privateRow 18 8, 7418157717805470452204388000⟩, ⟨.privateRow 18 9, 57726754604013479155335964800⟩, ⟨.privateRow 18 10, 23738104696977505447054041600⟩, ⟨.privateRow 18 12, 99403313418593304059538799200⟩, ⟨.privateRow 18 14, 198806626837186608119077598400⟩, ⟨.privateRow 18 16, 1630511066373642405394524482400⟩, ⟨.privateRow 18 17, 4221426285279166385334443731200⟩, ⟨.privateRow 19 8, 1689721452521216978640301324800⟩, ⟨.privateRow 19 13, 5376680713865404983757740422400⟩, ⟨.privateRow 19 17, 124447013873904572306180813088000⟩, ⟨.hall 13 9, 15161186673761800171500⟩, ⟨.hall 12 10, 16897791684347114060520⟩, ⟨.hall 13 15, 35862404452841591474850⟩, ⟨.hall 17 16, 176382202082804994033838080⟩, ⟨.hall 17 19, 58158356507594888345282401920⟩, ⟨.hall 8 20, 10680144820800293041280⟩, ⟨.hall 16 20, 2194278585434895461492390400⟩, ⟨.hall 15 21, 2808585916687846566930859200⟩, ⟨.hall 9 25, 19039919140452064328258400⟩, ⟨.hall 4 28, 11473647902207315478173520⟩, ⟨.hall 6 30, 320891525553208761031583102400⟩, ⟨.hall 5 31, 578027212993589202030149562600⟩, ⟨.hall 3 33, 1278469429350451999678319702400⟩]
  caps := #[0, 0, 5251129543022105692128009600, 0, 106188714093188768639162400, 42889094488173495251666592, 0, 6299148504753509653329840, 36597282947654602132521870, 5286434479551315488604960, 14892327836268031995452640, 34944440786622432539984400, 0, 236806710480806899035723120, 0, 1071929972089969275675640248, 0, 22341955520422797266301465600, 2648639482998297719688014400, 0] }

theorem case_56_37_24_checked :
    (Witness.linear .conditional case_56_37_24).check 56 37 24 = true := by
  change case_56_37_24.check 56 37 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_38_1_checked :
    (Witness.rising).check 56 38 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_38_2_checked :
    (Witness.rising).check 56 38 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_38_3_checked :
    (Witness.rising).check 56 38 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_38_4_checked :
    (Witness.rising).check 56 38 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_38_5_checked :
    (Witness.rising).check 56 38 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_38_6_checked :
    (Witness.rising).check 56 38 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_38_7_checked :
    (Witness.rising).check 56 38 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_38_8_checked :
    (Witness.rising).check 56 38 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_38_9_checked :
    (Witness.rising).check 56 38 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_38_10_checked :
    (Witness.rising).check 56 38 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_38_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_38_11_checked :
    (Witness.linear .positive case_56_38_11).check 56 38 11 = true := by
  change case_56_38_11.check 56 38 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_38_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_38_12_checked :
    (Witness.linear .positive case_56_38_12).check 56 38 12 = true := by
  change case_56_38_12.check 56 38 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_38_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_56_38_13_checked :
    (Witness.linear .positive case_56_38_13).check 56 38 13 = true := by
  change case_56_38_13.check 56 38 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_38_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_56_38_14_checked :
    (Witness.linear .positive case_56_38_14).check 56 38 14 = true := by
  change case_56_38_14.check 56 38 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_38_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_56_38_15_checked :
    (Witness.linear .positive case_56_38_15).check 56 38 15 = true := by
  change case_56_38_15.check 56 38 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_38_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_56_38_16_checked :
    (Witness.linear .positive case_56_38_16).check 56 38 16 = true := by
  change case_56_38_16.check 56 38 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_38_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_56_38_17_checked :
    (Witness.linear .positive case_56_38_17).check 56 38 17 = true := by
  change case_56_38_17.check 56 38 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_38_18 : Certificate := {
  objectiveScale := 13
  eta := 414407100
  rows := #[⟨.assumptionRow 18, 33⟩]
  caps := #[0, 0, 115354890, 32353295, 9152528, 2615008, 764218, 226746, 68510, 21164, 6721, 2211, 131560, 275770, 130548, 41998, 10120, 1797, 214] }

theorem case_56_38_18_checked :
    (Witness.linear .conditional case_56_38_18).check 56 38 18 = true := by
  change case_56_38_18.check 56 38 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_38_19 : Certificate := {
  objectiveScale := 987507669067920000
  eta := 1533899820402491820146668800
  rows := #[⟨.count 2, 193837132067530703892940800⟩, ⟨.count 3, 24025250360747430994399200⟩, ⟨.count 4, 2913502905309510579985920⟩, ⟨.count 5, 342421533149532493456800⟩, ⟨.count 6, 39203896460769373132800⟩, ⟨.count 7, 5717234900528866915200⟩, ⟨.count 8, 1559245881962418249600⟩, ⟨.count 9, 467773764588725474880⟩, ⟨.path 7, 1235880647376415840800⟩, ⟨.privateRow 2 35, 6689164833618774290784000⟩, ⟨.privateRow 2 36, 19993170447149447602454400⟩, ⟨.privateRow 3 32, 1788422542321686181911000⟩, ⟨.privateRow 3 33, 4208599541151812157951600⟩, ⟨.privateRow 3 34, 5983086323403459226756800⟩, ⟨.privateRow 4 29, 337245393694946537160360⟩, ⟨.privateRow 4 30, 901922391732931400207376⟩, ⟨.privateRow 4 31, 1451641673962407615187500⟩, ⟨.privateRow 4 32, 2151061987699815102953040⟩, ⟨.privateRow 4 33, 3339937163452707441023400⟩, ⟨.privateRow 5 25, 117974688423611539520⟩, ⟨.privateRow 5 26, 50168736252140807180880⟩, ⟨.privateRow 5 27, 179591182834572080732160⟩, ⟨.privateRow 5 28, 332511659321949124137120⟩, ⟨.privateRow 5 29, 517720122678176880029568⟩, ⟨.privateRow 5 30, 750938385488393351929680⟩, ⟨.privateRow 5 31, 1210597265258889812784480⟩, ⟨.privateRow 5 32, 1291114990108004688506880⟩, ⟨.privateRow 6 23, 5431373155502423569440⟩, ⟨.privateRow 6 24, 31149855231849739184800⟩, ⟨.privateRow 6 25, 74400623817150210079500⟩, ⟨.privateRow 6 26, 126508406957110692914400⟩, ⟨.privateRow 6 27, 194692267059081235844400⟩, ⟨.privateRow 6 28, 276755006577743793459360⟩, ⟨.privateRow 6 29, 439920806899622991742800⟩, ⟨.privateRow 6 30, 501347050920186115444800⟩, ⟨.privateRow 6 31, 402656686565818769884800⟩, ⟨.privateRow 7 20, 110601270397135818300⟩, ⟨.privateRow 7 21, 4204395146005806351600⟩, ⟨.privateRow 7 22, 15222137922658108161720⟩, ⟨.privateRow 7 23, 31320011032460717366800⟩, ⟨.privateRow 7 24, 52182530152371733964850⟩, ⟨.privateRow 7 25, 78801582060095581486800⟩, ⟨.privateRow 7 26, 110584254817074720481800⟩, ⟨.privateRow 7 27, 173334310966391254439760⟩, ⟨.privateRow 7 28, 202527941677216781125500⟩, ⟨.privateRow 7 29, 107980871067726754297200⟩, ⟨.privateRow 8 18, 79961327280124012800⟩, ⟨.privateRow 8 19, 2506704317182637672100⟩, ⟨.privateRow 8 20, 7424136642525605074800⟩, ⟨.privateRow 8 21, 14462005555201429265040⟩, ⟨.privateRow 8 22, 23792937161796900697600⟩, ⟨.privateRow 8 23, 35489085959248790368500⟩, ⟨.privateRow 8 24, 49190495085719147160000⟩, ⟨.privateRow 8 25, 76392220119755977437000⟩, ⟨.privateRow 8 26, 64851634973953579031280⟩, ⟨.privateRow 9 16, 37124901951486148800⟩, ⟨.privateRow 9 17, 1447300023770244631680⟩, ⟨.privateRow 9 18, 3950089567638126232320⟩, ⟨.privateRow 9 19, 7569430008799375866240⟩, ⟨.privateRow 9 20, 12354424871415560597664⟩, ⟨.privateRow 9 21, 18312476635936400998080⟩, ⟨.privateRow 9 22, 25240292714266645415400⟩, ⟨.privateRow 9 23, 25423132856377714698240⟩, ⟨.privateRow 10 14, 13859963395221495552⟩, ⟨.privateRow 10 15, 868722705664775881920⟩, ⟨.privateRow 10 16, 2394841752039714183360⟩, ⟨.privateRow 10 17, 4608437828911147271040⟩, ⟨.privateRow 10 18, 7536355096151688206400⟩, ⟨.privateRow 10 19, 11169398001124122727968⟩, ⟨.privateRow 10 20, 4747037462863362226560⟩, ⟨.privateRow 11 12, 4060536150943797525⟩, ⟨.privateRow 11 13, 567392251491879974160⟩, ⟨.privateRow 11 14, 1684542426048684001800⟩, ⟨.privateRow 11 15, 3338385413945177534400⟩, ⟨.privateRow 11 16, 4509902151648244451100⟩, ⟨.privateRow 12 11, 414754763989259318625⟩, ⟨.privateRow 12 12, 1388471332985581965120⟩, ⟨.privateRow 12 13, 1363677202039410858600⟩, ⟨.privateRow 13 9, 348318933015414160800⟩, ⟨.privateRow 13 10, 599799197153698091550⟩, ⟨.privateRow 14 7, 265443048953125963920⟩, ⟨.privateRow 15 5, 97794807509046407760⟩, ⟨.hall 5 32, 70945687629290030356800⟩, ⟨.hall 4 33, 612736242765798180949920⟩, ⟨.hall 3 34, 1926320206252835120167440⟩, ⟨.hall 2 35, 4979711598360643083139200⟩, ⟨.assumptionRow 19, 1078408757666508840⟩]
  caps := #[0, 739135274769270278499600, 149055750388499398844400, 17076322111463598220380, 390281240544604231680, 4943475328337843677952, 0, 0, 0, 168575937493498701432, 163854238615810571664, 69021580583311913700, 1370432282258224894995, 9172676592923603760, 555558553800341451360, 1078408757666508840, 4291219725081777928440, 902189334157100229240, 147386537345882732040] }

theorem case_56_38_19_checked :
    (Witness.linear .conditional case_56_38_19).check 56 38 19 = true := by
  change case_56_38_19.check 56 38 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_38_20 : Certificate := {
  objectiveScale := 30997717951200000
  eta := 61587852895710934551158400
  rows := #[⟨.count 2, 6888477577958846623353600⟩, ⟨.count 3, 728789909223514212874800⟩, ⟨.count 4, 71620409456439194070720⟩, ⟨.count 5, 6513413516311256755200⟩, ⟨.count 6, 688918737302152156800⟩, ⟨.count 7, 146134277609547427200⟩, ⟨.count 8, 53139737312562700800⟩, ⟨.count 9, 11956440895326607680⟩, ⟨.path 6, 227210326264905984000⟩, ⟨.privateRow 2 35, 170977104803170489824000⟩, ⟨.privateRow 2 36, 676309436776985493081600⟩, ⟨.privateRow 3 32, 52124270144855447939400⟩, ⟨.privateRow 3 33, 132269788021341615044400⟩, ⟨.privateRow 3 34, 201966705048745141104600⟩, ⟨.privateRow 4 28, 27139222984630236480⟩, ⟨.privateRow 4 29, 9229597416689666256240⟩, ⟨.privateRow 4 30, 26539446156669908253792⟩, ⟨.privateRow 4 31, 45985717146019396325580⟩, ⟨.privateRow 4 32, 72491126193862747491120⟩, ⟨.privateRow 4 33, 119493998801326931221440⟩, ⟨.privateRow 5 26, 1175467595521797117540⟩, ⟨.privateRow 5 27, 4793949888642183915360⟩, ⟨.privateRow 5 28, 9697749013174537835520⟩, ⟨.privateRow 5 29, 16283533790778141888000⟩, ⟨.privateRow 5 30, 25398920310740822565720⟩, ⟨.privateRow 5 31, 43933878808285581155040⟩, ⟨.privateRow 5 32, 51367764304158880097520⟩, ⟨.privateRow 6 23, 77764312013652023760⟩, ⟨.privateRow 6 24, 705735777185790551200⟩, ⟨.privateRow 6 25, 1946717341012899655200⟩, ⟨.privateRow 6 26, 3631735031816864887200⟩, ⟨.privateRow 6 27, 6070661449029949371600⟩, ⟨.privateRow 6 28, 9355725215816954214240⟩, ⟨.privateRow 6 29, 16133485202161195869000⟩, ⟨.privateRow 6 30, 20446621008869177522400⟩, ⟨.privateRow 6 31, 19268848319087467900800⟩, ⟨.privateRow 7 21, 52665275372271962400⟩, ⟨.privateRow 7 22, 335586930367639270320⟩, ⟨.privateRow 7 23, 797649598618779706800⟩, ⟨.privateRow 7 24, 1467214242606572159700⟩, ⟨.privateRow 7 25, 2423144909341985400000⟩, ⟨.privateRow 7 26, 3708157294342265965200⟩, ⟨.privateRow 7 27, 6359450616686912144400⟩, ⟨.privateRow 7 28, 8324434742401005228000⟩, ⟨.privateRow 7 29, 8611484216276901960000⟩, ⟨.privateRow 7 30, 1658363096801203392600⟩, ⟨.privateRow 8 19, 27123407586620545200⟩, ⟨.privateRow 8 20, 156248943518472714000⟩, ⟨.privateRow 8 21, 355371993277763061600⟩, ⟨.privateRow 8 22, 649854704218214695200⟩, ⟨.privateRow 8 23, 1064870517240025996500⟩, ⟨.privateRow 8 24, 1616017368630254990400⟩, ⟨.privateRow 8 25, 2759668337206055675400⟩, ⟨.privateRow 8 26, 3737716273222378967520⟩, ⟨.privateRow 8 27, 2405403421788971003400⟩, ⟨.privateRow 9 17, 13489317933188993280⟩, ⟨.privateRow 9 18, 76609787958944560320⟩, ⟨.privateRow 9 19, 177172715085294277440⟩, ⟨.privateRow 9 20, 324152397606632474880⟩, ⟨.privateRow 9 21, 529183217404270228800⟩, ⟨.privateRow 9 22, 798922738158559854840⟩, ⟨.privateRow 9 23, 1355063301470348870400⟩, ⟨.privateRow 9 24, 1441858205747534615040⟩, ⟨.privateRow 10 15, 7116929104361076000⟩, ⟨.privateRow 10 16, 41081104614711934080⟩, ⟨.privateRow 10 17, 100633377535665614640⟩, ⟨.privateRow 10 18, 187196801896527696000⟩, ⟨.privateRow 10 19, 306350585606923970112⟩, ⟨.privateRow 10 20, 462463325000719282240⟩, ⟨.privateRow 10 21, 590681392564954771080⟩, ⟨.privateRow 11 13, 4096188084510041520⟩, ⟨.privateRow 11 14, 24909251865263766000⟩, ⟨.privateRow 11 15, 65913712628082580800⟩, ⟨.privateRow 11 16, 127867492908353998800⟩, ⟨.privateRow 11 17, 212558949250250803200⟩, ⟨.privateRow 11 18, 155599793318347658280⟩, ⟨.privateRow 12 11, 2772636963574002525⟩, ⟨.privateRow 12 12, 17396937810660408000⟩, ⟨.privateRow 12 13, 50326855809410466000⟩, ⟨.privateRow 12 14, 104180892966147135600⟩, ⟨.privateRow 12 15, 24573174657557826300⟩, ⟨.privateRow 13 9, 2149033494258050400⟩, ⟨.privateRow 13 10, 14352473693794836600⟩, ⟨.privateRow 13 11, 45579977063930268960⟩, ⟨.privateRow 13 12, 2236749147084909600⟩, ⟨.privateRow 14 7, 2261601915385853040⟩, ⟨.privateRow 14 8, 14367823933039536960⟩, ⟨.privateRow 14 9, 2544302154809084670⟩, ⟨.privateRow 15 5, 2499665274900153360⟩, ⟨.privateRow 15 6, 2638535567950161880⟩, ⟨.hall 5 32, 5943901033982273762400⟩, ⟨.hall 4 33, 27155187233444724854400⟩, ⟨.hall 3 34, 74090078748040545590400⟩, ⟨.hall 2 35, 176465258784506826534400⟩, ⟨.assumptionRow 20, 27212320917453672⟩]
  caps := #[0, 0, 3325639412969218144800, 171289502575545954600, 179860747759397292588, 19874973333538168560, 19625064601638415920, 6126838531350368832, 0, 11399430640317115200, 15341495046538594248, 1783079999671904934, 486750921161649144, 8830520478785010720, 120046394901257790966, 58507742959328254592, 432394444415577844200, 113816577635287887360, 24821737497672875760] }

theorem case_56_38_20_checked :
    (Witness.linear .conditional case_56_38_20).check 56 38 20 = true := by
  change case_56_38_20.check 56 38 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_38_21 : Certificate := {
  objectiveScale := 51662863252000000
  eta := 109191678364131447151267200
  rows := #[⟨.count 2, 12184968335639283574790400⟩, ⟨.count 3, 1269505003163540886943200⟩, ⟨.count 4, 120633846166681401153600⟩, ⟨.count 5, 9430879987159007176800⟩, ⟨.count 6, 563660785065397219200⟩, ⟨.count 7, 73067138804773713600⟩, ⟨.count 8, 26569868656281350400⟩, ⟨.count 9, 11956440895326607680⟩, ⟨.path 6, 406386254695284864000⟩, ⟨.privateRow 2 35, 343853955215265096201600⟩, ⟨.privateRow 2 36, 1295626505286247489555200⟩, ⟨.privateRow 3 32, 91603358580309745068900⟩, ⟨.privateRow 3 33, 244671403216018511132400⟩, ⟨.privateRow 3 34, 383511144801556029258000⟩, ⟨.privateRow 4 29, 15522504746250802340040⟩, ⟨.privateRow 4 30, 46363291585793064490608⟩, ⟨.privateRow 4 31, 83814401583720867199140⟩, ⟨.privateRow 4 32, 137256620244767420997600⟩, ⟨.privateRow 4 33, 235046025464136320594160⟩, ⟨.privateRow 5 25, 104033688107749239840⟩, ⟨.privateRow 5 26, 1857340573010631809100⟩, ⟨.privateRow 5 27, 7922714595584555463840⟩, ⟨.privateRow 5 28, 16699668543209138847360⟩, ⟨.privateRow 5 29, 29245226688237542830848⟩, ⟨.privateRow 5 30, 47720931215599192070520⟩, ⟨.privateRow 5 31, 86660062193755116786720⟩, ⟨.privateRow 5 32, 107620588745551202761440⟩, ⟨.privateRow 6 22, 1423385820872215200⟩, ⟨.privateRow 6 23, 192584101564010716560⟩, ⟨.privateRow 6 24, 1090208102801385568000⟩, ⟨.privateRow 6 25, 3149063205452167103100⟩, ⟨.privateRow 6 26, 6127947079963624000800⟩, ⟨.privateRow 6 27, 10719993078928943409600⟩, ⟨.privateRow 6 28, 17377453240312468343040⟩, ⟨.privateRow 6 29, 31699395308249595927000⟩, ⟨.privateRow 6 30, 43154843933124208084800⟩, ⟨.privateRow 6 31, 44693603082477121172400⟩, ⟨.privateRow 7 20, 434923445266510200⟩, ⟨.privateRow 7 21, 121699487684574399600⟩, ⟨.privateRow 7 22, 504685165887258436080⟩, ⟨.privateRow 7 23, 1256638807856703471200⟩, ⟨.privateRow 7 24, 2415129891564931140600⟩, ⟨.privateRow 7 25, 4189803944014549832400⟩, ⟨.privateRow 7 26, 6771758042799563814000⟩, ⟨.privateRow 7 27, 12361394161364752904400⟩, ⟨.privateRow 7 28, 17487184425553208866500⟩, ⟨.privateRow 7 29, 20082155161735841974800⟩, ⟨.privateRow 7 30, 11821219242343747236000⟩, ⟨.privateRow 8 19, 62688283860913811100⟩, ⟨.privateRow 8 20, 232788281068101376800⟩, ⟨.privateRow 8 21, 543519875700055374120⟩, ⟨.privateRow 8 22, 1040653189037686224000⟩, ⟨.privateRow 8 23, 1794088865595622746150⟩, ⟨.privateRow 8 24, 2881407363385654303200⟩, ⟨.privateRow 8 25, 5257789529826841807800⟩, ⟨.privateRow 8 26, 7715889857784104156160⟩, ⟨.privateRow 8 27, 9446003461505774463300⟩, ⟨.privateRow 8 28, 1015743937172422458000⟩, ⟨.privateRow 9 17, 31883842387537620480⟩, ⟨.privateRow 9 18, 115689636440891713200⟩, ⟨.privateRow 9 19, 264370193129999436480⟩, ⟨.privateRow 9 20, 503631860379812996832⟩, ⟨.privateRow 9 21, 864554003999110384960⟩, ⟨.privateRow 9 22, 1380138615014714394840⟩, ⟨.privateRow 9 23, 2503261196973935798400⟩, ⟨.privateRow 9 24, 3800598295708911496800⟩, ⟨.privateRow 9 25, 2341336825991512597248⟩, ⟨.privateRow 10 15, 17270414626582877760⟩, ⟨.privateRow 10 16, 64483027392744354240⟩, ⟨.privateRow 10 17, 148569848903039884320⟩, ⟨.privateRow 10 18, 282606784798628908800⟩, ⟨.privateRow 10 19, 483438760201039170528⟩, ⟨.privateRow 10 20, 768902476836497523520⟩, ⟨.privateRow 10 21, 1381134985089324945480⟩, ⟨.privateRow 10 22, 1336084823858719334400⟩, ⟨.privateRow 11 13, 10517239676444701200⟩, ⟨.privateRow 11 14, 41396804290366925400⟩, ⟨.privateRow 11 15, 98615089435813473600⟩, ⟨.privateRow 11 16, 189448698908589420300⟩, ⟨.privateRow 11 17, 324273169736888299200⟩, ⟨.privateRow 11 18, 514957266894552922440⟩, ⟨.privateRow 11 19, 471246142695434506400⟩, ⟨.privateRow 12 11, 7339333138872359625⟩, ⟨.privateRow 12 12, 31314488059188734400⟩, ⟨.privateRow 12 13, 78472615910228911800⟩, ⟨.privateRow 12 14, 154966569113421172800⟩, ⟨.privateRow 12 15, 268347765729436793400⟩, ⟨.privateRow 12 16, 45311115297765517200⟩, ⟨.privateRow 13 9, 6140095697880144000⟩, ⟨.privateRow 13 10, 28052562219689907900⟩, ⟨.privateRow 13 11, 75850648854479378880⟩, ⟨.privateRow 13 12, 94689047226594506400⟩, ⟨.privateRow 14 7, 6030938441028941440⟩, ⟨.privateRow 14 8, 31130285188252330080⟩, ⟨.privateRow 14 9, 32227827294248405820⟩, ⟨.privateRow 15 5, 7498995824700460080⟩, ⟨.privateRow 15 6, 15831213407700971280⟩, ⟨.privateRow 16 3, 11873410055775728460⟩, ⟨.hall 5 32, 16863326281813424212800⟩, ⟨.hall 4 33, 60875671791847793680800⟩, ⟨.hall 3 34, 153105926467791479101920⟩, ⟨.hall 2 35, 346809115051369277507200⟩, ⟨.assumptionRow 21, 31051034026076064⟩]
  caps := #[0, 25402814091869772317760, 0, 677351610116580399000, 100914412099545044000, 9074443003802702240, 12919155017405661024, 14300508814620136680, 30867627698782211610, 0, 16687616318012940552, 1678461001447449989, 1940684413202079875, 18582579481305828560, 12263005236787853548, 0, 0, 597542804360343922080, 161912426023887739200] }

theorem case_56_38_21_checked :
    (Witness.linear .conditional case_56_38_21).check 56 38 21 = true := by
  change case_56_38_21.check 56 38 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_38_22 : Certificate := {
  objectiveScale := 292494866664000000
  eta := 623270896663897888322716800
  rows := #[⟨.count 2, 79696621017686539407340800⟩, ⟨.count 3, 9810775089307535626483200⟩, ⟨.count 4, 1137158021715191629433280⟩, ⟨.count 5, 117553350250670069736000⟩, ⟨.count 6, 9800974115192343283200⟩, ⟨.count 7, 510467401832934546000⟩, ⟨.path 7, 530482239676422633600⟩, ⟨.privateRow 2 35, 5377876171790332029019200⟩, ⟨.privateRow 2 36, 12061732144430043800524800⟩, ⟨.privateRow 3 32, 955594976231253470112000⟩, ⟨.privateRow 3 33, 2382793769435894069455200⟩, ⟨.privateRow 3 34, 3531719766321340949955600⟩, ⟨.privateRow 4 29, 143737411008117709462680⟩, ⟨.privateRow 4 30, 440157663774073473372144⟩, ⟨.privateRow 4 31, 775690949803272348065220⟩, ⟨.privateRow 4 32, 1268817773995942107537600⟩, ⟨.privateRow 4 33, 2173713127877148518540880⟩, ⟨.privateRow 5 25, 522459334447422532160⟩, ⟨.privateRow 5 26, 18296610159983325370200⟩, ⟨.privateRow 5 27, 73847339659775778370560⟩, ⟨.privateRow 5 28, 155006100443437318835760⟩, ⟨.privateRow 5 29, 267900293177720615700288⟩, ⟨.privateRow 5 30, 436653815527892210648400⟩, ⟨.privateRow 5 31, 800247591867733560751200⟩, ⟨.privateRow 5 32, 1006597962065818387465200⟩, ⟨.privateRow 6 22, 159106722649226352000⟩, ⟨.privateRow 6 23, 2129378304788812677600⟩, ⟨.privateRow 6 24, 10864042736152359353600⟩, ⟨.privateRow 6 25, 29388337562667517434000⟩, ⟨.privateRow 6 26, 56184750848273114152800⟩, ⟨.privateRow 6 27, 97304809977963666078000⟩, ⟨.privateRow 6 28, 157585662380699748074880⟩, ⟨.privateRow 6 29, 290288226639480363894600⟩, ⟨.privateRow 6 30, 402763641640488527599200⟩, ⟨.privateRow 6 31, 428646769710569894484000⟩, ⟨.privateRow 7 19, 33657191329644036000⟩, ⟨.privateRow 7 20, 229710330824820545700⟩, ⟨.privateRow 7 21, 1422679278355165630800⟩, ⟨.privateRow 7 22, 5062378147891759454760⟩, ⟨.privateRow 7 23, 11747232367895055631600⟩, ⟨.privateRow 7 24, 21968329257453075997500⟩, ⟨.privateRow 7 25, 37662076553192346340800⟩, ⟨.privateRow 7 26, 60811252341212016844200⟩, ⟨.privateRow 7 27, 112145312747822866031520⟩, ⟨.privateRow 7 28, 161953075622953240926300⟩, ⟨.privateRow 7 29, 192217715558767295997600⟩, ⟨.privateRow 7 30, 134442528859885447000800⟩, ⟨.privateRow 8 16, 4949986926864819840⟩, ⟨.privateRow 8 17, 25854842430499282200⟩, ⟨.privateRow 8 18, 167062058781687669600⟩, ⟨.privateRow 8 19, 784263553725144893400⟩, ⟨.privateRow 8 20, 2362493760549118560000⟩, ⟨.privateRow 8 21, 5112098998719642689760⟩, ⟨.privateRow 8 22, 9437975073888923161600⟩, ⟨.privateRow 8 23, 16005473353834465901400⟩, ⟨.privateRow 8 24, 25628115350724134648400⟩, ⟨.privateRow 8 25, 47210500314973219224000⟩, ⟨.privateRow 8 26, 70728506952873836386320⟩, ⟨.privateRow 8 27, 89491896460429329566700⟩, ⟨.privateRow 8 28, 27163053261170698872000⟩, ⟨.privateRow 9 13, 873527104740850560⟩, ⟨.privateRow 9 14, 3248428920755038020⟩, ⟨.privateRow 9 15, 20294946400145761344⟩, ⟨.privateRow 9 16, 109253282885802095040⟩, ⟨.privateRow 9 17, 443214214066973099520⟩, ⟨.privateRow 9 18, 1207178061789157938480⟩, ⟨.privateRow 9 19, 2521793339831859125760⟩, ⟨.privateRow 9 20, 4588637881203687991680⟩, ⟨.privateRow 9 21, 7696404673453650714560⟩, ⟨.privateRow 9 22, 12191817800868051265920⟩, ⟨.privateRow 9 23, 19032346163300456226240⟩, ⟨.privateRow 9 24, 40841104636829912294880⟩, ⟨.privateRow 9 25, 28139190683148441344448⟩, ⟨.privateRow 10 11, 412498910572068320⟩, ⟨.privateRow 10 12, 3057344866592976960⟩, ⟨.privateRow 10 13, 15778083329381613240⟩, ⟨.privateRow 10 14, 77219796059091189504⟩, ⟨.privateRow 10 15, 278967120378310203840⟩, ⟨.privateRow 10 16, 712226965130818885440⟩, ⟨.privateRow 10 17, 1455914904864115135440⟩, ⟨.privateRow 10 18, 2614268095601924623680⟩, ⟨.privateRow 10 19, 4332476057738433564960⟩, ⟨.privateRow 10 20, 4883987101173288908800⟩, ⟨.privateRow 10 21, 15989695270505084288160⟩, ⟨.privateRow 10 22, 14810714455674317019840⟩, ⟨.privateRow 11 9, 488485551993238800⟩, ⟨.privateRow 11 10, 3093741829290512400⟩, ⟨.privateRow 11 11, 14194815452038821600⟩, ⟨.privateRow 11 12, 62068195450140905025⟩, ⟨.privateRow 11 13, 204805709099031920880⟩, ⟨.privateRow 11 14, 502512065700473228400⟩, ⟨.privateRow 11 15, 1013081459022285483600⟩, ⟨.privateRow 11 16, 1802878051019046101100⟩, ⟨.privateRow 11 17, 2958179687316146311200⟩, ⟨.privateRow 11 18, 4584925391008539376800⟩, ⟨.privateRow 11 19, 5924515603091331246000⟩, ⟨.privateRow 12 7, 729239145475620780⟩, ⟨.privateRow 12 8, 3838100765661162000⟩, ⟨.privateRow 12 9, 15395048626707549800⟩, ⟨.privateRow 12 10, 59197060044491569200⟩, ⟨.privateRow 12 11, 182309786368905195000⟩, ⟨.privateRow 12 12, 435598849564104145920⟩, ⟨.privateRow 12 13, 870919893739455674400⟩, ⟨.privateRow 12 14, 1545986988408316053600⟩, ⟨.privateRow 12 15, 2523167443345647898800⟩, ⟨.privateRow 12 16, 597976099290009039600⟩, ⟨.privateRow 13 5, 1389026943763087200⟩, ⟨.privateRow 13 6, 4375434872853724680⟩, ⟨.privateRow 13 7, 19958123981438042400⟩, ⟨.privateRow 13 8, 69682851678781541200⟩, ⟨.privateRow 13 9, 200755247107406191200⟩, ⟨.privateRow 13 10, 472182346695464455050⟩, ⟨.privateRow 13 11, 945093932536404530880⟩, ⟨.privateRow 13 12, 527135725158091592400⟩, ⟨.privateRow 14 3, 3447312324066570960⟩, ⟨.privateRow 14 4, 7222940107568053440⟩, ⟨.privateRow 14 5, 30336348451785824448⟩, ⟨.privateRow 14 6, 103782244703477820480⟩, ⟨.privateRow 14 7, 286509957600199453120⟩, ⟨.privateRow 14 8, 352436989366335313440⟩, ⟨.privateRow 15 1, 11541002128396781040⟩, ⟨.privateRow 15 3, 88481016317708654640⟩, ⟨.privateRow 15 4, 145993676924219280156⟩, ⟨.privateRow 16 0, 57705010641983905200⟩, ⟨.hall 5 32, 169515838015433516006400⟩, ⟨.hall 4 33, 580383419387511298759200⟩, ⟨.hall 3 34, 1433164941733491811484640⟩, ⟨.hall 2 35, 3218349500196122798105600⟩, ⟨.assumptionRow 22, 9626756048749840⟩]
  caps := #[0, 0, 0, 2892519928242766021200, 0, 300767100383401981472, 265384921518624536200, 20024464599536837440, 21382112808320943560, 43259458335708618976, 1036528959471005000, 227842567851153995250, 1771009353297936180, 376012689656681454520, 15138197596987985520, 2093486054796569336904, 7224686142046271939040, 9781684679025317298240, 3082035652610957842800] }

theorem case_56_38_22_checked :
    (Witness.linear .conditional case_56_38_22).check 56 38 22 = true := by
  change case_56_38_22.check 56 38 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_38_23 : Certificate := {
  objectiveScale := 8559268142724048750000
  eta := 15888265383653417452305063456000
  rows := #[⟨.count 2, 1934096201106087573404898048000⟩, ⟨.count 3, 221549777906734260386985582000⟩, ⟨.count 4, 23077284217743090364490260800⟩, ⟨.count 5, 2055799533488613492139560000⟩, ⟨.count 6, 138011716933501325346432000⟩, ⟨.count 7, 5031677179867235819922000⟩, ⟨.path 6, 38549331403790455920672000⟩, ⟨.path 7, 5460905104925505947712000⟩, ⟨.privateRow 2 36, 838840966010026618010836464000⟩, ⟨.privateRow 3 35, 850418855200901127632476986000⟩, ⟨.privateRow 4 28, 3737817333615660894799200⟩, ⟨.privateRow 4 29, 3338182363696586484130252200⟩, ⟨.privateRow 4 30, 8090131836877736440703388480⟩, ⟨.privateRow 4 33, 187012345744125553719040974000⟩, ⟨.privateRow 5 26, 355559873860189742617773900⟩, ⟨.privateRow 5 27, 1657455000506144488208102400⟩, ⟨.privateRow 5 28, 3435054129592792362320464800⟩, ⟨.privateRow 5 32, 156906096030518213041880817600⟩, ⟨.privateRow 6 22, 261385827525570691944000⟩, ⟨.privateRow 6 23, 31340160720315925964085600⟩, ⟨.privateRow 6 24, 203822859730495012895888000⟩, ⟨.privateRow 6 25, 638483893573867459577959500⟩, ⟨.privateRow 6 26, 1288520107203552552415944000⟩, ⟨.privateRow 6 28, 6965278838987645013577740000⟩, ⟨.privateRow 6 30, 18358433596258457548686840000⟩, ⟨.privateRow 7 19, 165879467468150631426000⟩, ⟨.privateRow 7 20, 2156433077085958208538000⟩, ⟨.privateRow 7 21, 20649480374520084663576000⟩, ⟨.privateRow 7 22, 92151573494139947444857200⟩, ⟨.privateRow 7 23, 245034691870359991992392000⟩, ⟨.privateRow 7 24, 495979607729770387963740000⟩, ⟨.privateRow 7 25, 730106627527674422033580000⟩, ⟨.privateRow 7 26, 874313810920740166995018000⟩, ⟨.privateRow 7 27, 4623104992862016271344333600⟩, ⟨.privateRow 7 28, 3082800786450801088955782500⟩, ⟨.privateRow 7 29, 9437988767379543759367980000⟩, ⟨.privateRow 7 30, 8822327123871502690830381000⟩, ⟨.privateRow 8 16, 30495013211316580726800⟩, ⟨.privateRow 8 17, 130692913762785345972000⟩, ⟨.privateRow 8 18, 1618581470446803130884000⟩, ⟨.privateRow 8 19, 11130679822130551965282000⟩, ⟨.privateRow 8 20, 41417772488824519641672000⟩, ⟨.privateRow 8 21, 101685621553135138433514600⟩, ⟨.privateRow 8 22, 205282263934179449259242000⟩, ⟨.privateRow 8 23, 362852538448153164923011500⟩, ⟨.privateRow 8 24, 586223064682973669357406000⟩, ⟨.privateRow 8 25, 985598826989751889090176000⟩, ⟨.privateRow 8 26, 3026416596130691421069812400⟩, ⟨.privateRow 8 27, 3046223107211441540251869000⟩, ⟨.privateRow 9 14, 22871259908487435545100⟩, ⟨.privateRow 9 15, 121980052845266322907200⟩, ⟨.privateRow 9 16, 1045543310102282767776000⟩, ⟨.privateRow 9 17, 6108385723251413554814400⟩, ⟨.privateRow 9 18, 20248688772314209602595200⟩, ⟨.privateRow 9 19, 47638755183933102109939200⟩, ⟨.privateRow 9 20, 94998065155893412280127360⟩, ⟨.privateRow 9 21, 172032534529440604073454400⟩, ⟨.privateRow 9 22, 292065989031384551910927000⟩, ⟨.privateRow 9 23, 561090817366390047326990400⟩, ⟨.privateRow 9 24, 866119365227813525802573600⟩, ⟨.privateRow 9 25, 2052485161195589255765710080⟩, ⟨.privateRow 9 26, 2406148027412512169086700400⟩, ⟨.privateRow 10 12, 21525891678576409924800⟩, ⟨.privateRow 10 13, 91485039633949742180400⟩, ⟨.privateRow 10 14, 731880317071597937443200⟩, ⟨.privateRow 10 15, 3711678750863103825604800⟩, ⟨.privateRow 10 16, 11372294157574060258732800⟩, ⟨.privateRow 10 17, 26073236295675676521414000⟩, ⟨.privateRow 10 18, 51198354907872237532958400⟩, ⟨.privateRow 10 19, 91960761840046280839738080⟩, ⟨.privateRow 10 20, 155931167553865449449704000⟩, ⟨.privateRow 10 21, 305743002456660038366896800⟩, ⟨.privateRow 10 22, 522719377885636269749611200⟩, ⟨.privateRow 10 23, 782989959213764526741316800⟩, ⟨.privateRow 10 24, 1535558093247919632549577920⟩, ⟨.privateRow 10 25, 1968483597803696602495666800⟩, ⟨.privateRow 11 10, 25412511009430483939000⟩, ⟨.privateRow 11 11, 80722093794661537218000⟩, ⟨.privateRow 11 12, 571781497712185888627500⟩, ⟨.privateRow 11 13, 2592076122961909361778000⟩, ⟨.privateRow 11 14, 7612862226682246402869000⟩, ⟨.privateRow 11 15, 17171038208218259301552000⟩, ⟨.privateRow 11 16, 33315801933363364444029000⟩, ⟨.privateRow 11 17, 58924682346048538486194000⟩, ⟨.privateRow 11 18, 98117705007411098488479000⟩, ⟨.privateRow 11 19, 187950931425747859212844000⟩, ⟨.privateRow 11 20, 327402085589997639828106500⟩, ⟨.privateRow 11 21, 525385513326397090807440000⟩, ⟨.privateRow 11 22, 741028821034992911661240000⟩, ⟨.privateRow 11 23, 1218946668082746364811649600⟩, ⟨.privateRow 12 9, 79867891743924378094000⟩, ⟨.privateRow 12 10, 507396018137872519656000⟩, ⟨.privateRow 12 11, 2156433077085958208538000⟩, ⟨.privateRow 12 12, 6229695556026101491332000⟩, ⟨.privateRow 12 13, 13965471356366205541008000⟩, ⟨.privateRow 12 14, 26927766885663119168154000⟩, ⟨.privateRow 12 15, 47261824939467250737124500⟩, ⟨.privateRow 12 16, 77762283688857280853340000⟩, ⟨.privateRow 12 17, 144768540575037327733184400⟩, ⟨.privateRow 12 18, 250944915859410395971348000⟩, ⟨.privateRow 12 19, 417808908685404402904237500⟩, ⟨.privateRow 12 20, 645594988363781869384686000⟩, ⟨.privateRow 12 21, 895997943529215635647539000⟩, ⟨.privateRow 12 22, 1326493866818142426012008400⟩, ⟨.privateRow 13 7, 75664318494244147668000⟩, ⟨.privateRow 13 8, 559075242207470646658000⟩, ⟨.privateRow 13 9, 2283282081620426338452000⟩, ⟨.privateRow 13 11, 26835611625958591039584000⟩, ⟨.privateRow 13 12, 21358956192089490827424000⟩, ⟨.privateRow 13 13, 48547390812345418130676000⟩, ⟨.privateRow 13 14, 79428618339332794014483000⟩, ⟨.privateRow 13 15, 144023590966589451261144000⟩, ⟨.privateRow 13 16, 244108224326130469206501600⟩, ⟨.privateRow 13 17, 405409418492160143205144000⟩, ⟨.privateRow 13 18, 647828436907906611814957500⟩, ⟨.privateRow 13 19, 969984135531141011326188000⟩, ⟨.privateRow 13 20, 1330758812237267987802228000⟩, ⟨.privateRow 13 25, 15049027633957207017983856000⟩, ⟨.privateRow 14 5, 186890866680783044739960⟩, ⟨.privateRow 14 6, 786908912340139135747200⟩, ⟨.privateRow 14 7, 2907191259478847362621600⟩, ⟨.privateRow 14 8, 3078202510036426619246400⟩, ⟨.privateRow 14 9, 16119337251217537608821550⟩, ⟨.privateRow 14 10, 56814823470958045600947840⟩, ⟨.privateRow 14 11, 52329442670619252527188800⟩, ⟨.privateRow 14 12, 106959080623463527143484800⟩, ⟨.privateRow 14 13, 190940168792200010709325800⟩, ⟨.privateRow 14 15, 1154237992620516084313992960⟩, ⟨.privateRow 14 16, 512080974705345542587490400⟩, ⟨.privateRow 14 17, 1282071345430171686916125600⟩, ⟨.privateRow 14 18, 1876384301475061769189198400⟩, ⟨.privateRow 14 24, 24280861399167333172615603200⟩, ⟨.privateRow 15 3, 622969555602610149133200⟩, ⟨.privateRow 15 4, 1308236066765481313179720⟩, ⟨.privateRow 15 5, 4819817088083352206451600⟩, ⟨.privateRow 15 6, 8721573778436542087864800⟩, ⟨.privateRow 15 7, 19238765687727666370290000⟩, ⟨.privateRow 15 8, 68682393505187768941935300⟩, ⟨.privateRow 15 9, 169198531301668916504577120⟩, ⟨.privateRow 15 12, 1419436132440547224799996200⟩, ⟨.privateRow 15 18, 11540822502316154317767096600⟩, ⟨.privateRow 16 2, 6229695556026101491332000⟩, ⟨.privateRow 16 3, 9811770500741109848847900⟩, ⟨.privateRow 16 4, 27541811931904869751152000⟩, ⟨.privateRow 16 5, 50875847040879828845878000⟩, ⟨.privateRow 16 6, 115432594126365998221740000⟩, ⟨.privateRow 16 9, 1766118690133399772792622000⟩, ⟨.privateRow 16 11, 32705901669137032829493000⟩, ⟨.privateRow 16 12, 5619468559515362913431070000⟩, ⟨.privateRow 16 14, 886693334141048445599588000⟩, ⟨.privateRow 16 15, 1488118525945734993741931500⟩, ⟨.privateRow 16 16, 3429447403592368870978266000⟩, ⟨.privateRow 16 17, 20953581002693792366095182000⟩, ⟨.privateRow 16 19, 62173919073029499408866193000⟩, ⟨.privateRow 17 2, 287811934688405888899538400⟩, ⟨.privateRow 17 3, 137709059659524348755760000⟩, ⟨.privateRow 17 5, 1292845054215299180083488000⟩, ⟨.privateRow 17 8, 12222662680923211125993384000⟩, ⟨.privateRow 17 9, 845321766217695617746896000⟩, ⟨.privateRow 17 11, 30351076748959166465769504000⟩, ⟨.privateRow 17 12, 9576288008723323212475550400⟩, ⟨.privateRow 17 16, 44305594794457633806353184000⟩, ⟨.privateRow 18 12, 1709021453797235210590733776000⟩, ⟨.hall 16 9, 5022330411112064484033600⟩, ⟨.hall 14 10, 28162425883637128983900⟩, ⟨.hall 17 13, 115763044437593801747699200⟩, ⟨.hall 10 15, 195603962161794261075⟩, ⟨.hall 11 17, 556216198923939276800⟩, ⟨.hall 8 19, 49457619001301616336⟩, ⟨.hall 15 19, 4757222060965386593380800⟩, ⟨.hall 6 27, 116456980970548688570100⟩, ⟨.hall 9 27, 1533163078003433610333600⟩, ⟨.hall 3 32, 99761744984362371796485600⟩, ⟨.hall 4 32, 376706692023700269752320800⟩]
  caps := #[0, 0, 0, 188904701067678768890718000, 0, 4325063108337030505446000, 4693634713006523884746300, 3734227923132490742603700, 1410391438256626392651000, 2759942388373254891398480, 4324363197361236960210000, 0, 7729958265047195107235800, 1383049779849201931867400, 20122203572913235885521430, 200474116399379669930002920, 1197455373269154633580947000, 0, 0] }

theorem case_56_38_23_checked :
    (Witness.linear .conditional case_56_38_23).check 56 38 23 = true := by
  change case_56_38_23.check 56 38 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_38_24 : Certificate := {
  objectiveScale := 3369673353566520000
  eta := 5186701609322298869629425600
  rows := #[⟨.count 2, 573679479746077944506467200⟩, ⟨.count 3, 58014668873525786828406000⟩, ⟨.count 4, 5097682379706528154102560⟩, ⟨.count 5, 353250911173693315582800⟩, ⟨.count 6, 16721936623606784169600⟩, ⟨.path 3, 199136933684425805468400⟩, ⟨.path 5, 31974939080073442252800⟩, ⟨.path 6, 14784587366818821552000⟩, ⟨.privateRow 2 36, 298252461618650602448985600⟩, ⟨.privateRow 3 35, 298220759613801681253997400⟩, ⟨.privateRow 4 29, 823195392576987029860260⟩, ⟨.privateRow 4 30, 2219140339424483649174000⟩, ⟨.privateRow 5 25, 1207695422816045523360⟩, ⟨.privateRow 5 26, 72008839585406714330340⟩, ⟨.privateRow 5 27, 393104860126622817853680⟩, ⟨.privateRow 5 28, 909394653380482279090080⟩, ⟨.privateRow 5 29, 1648141943517057325729392⟩, ⟨.privateRow 5 32, 33558836561500864980366000⟩, ⟨.privateRow 6 22, 443384683201695034800⟩, ⟨.privateRow 6 23, 5225605194877120053000⟩, ⟨.privateRow 6 24, 39637183107808673587200⟩, ⟨.privateRow 6 25, 145446011257413174808500⟩, ⟨.privateRow 6 26, 324883340115788949580800⟩, ⟨.privateRow 6 27, 662722863270304980943800⟩, ⟨.privateRow 6 28, 1292187652589214246705840⟩, ⟨.privateRow 6 29, 1833490676042552189262600⟩, ⟨.privateRow 6 30, 2940041607197753900041200⟩, ⟨.privateRow 6 31, 7657601852572931725666200⟩, ⟨.privateRow 7 19, 80393926075032616200⟩, ⟨.privateRow 7 20, 377404819630014226050⟩, ⟨.privateRow 7 21, 3198703785955085608200⟩, ⟨.privateRow 7 22, 17244497143094496174900⟩, ⟨.privateRow 7 23, 53185048427860466317200⟩, ⟨.privateRow 7 24, 118621237923710625203100⟩, ⟨.privateRow 7 25, 243762040423886990662800⟩, ⟨.privateRow 7 26, 478607373570801117743100⟩, ⟨.privateRow 7 27, 1091872786785591311340840⟩, ⟨.privateRow 7 28, 1646152729806207435362550⟩, ⟨.privateRow 7 29, 2449879839918280039069800⟩, ⟨.privateRow 7 30, 3135711490605930506470200⟩, ⟨.privateRow 8 16, 14779489440056501160⟩, ⟨.privateRow 8 17, 31670334514406788200⟩, ⟨.privateRow 8 18, 238745598647066557200⟩, ⟨.privateRow 8 19, 1662692562006356380500⟩, ⟨.privateRow 8 20, 7456924217483052858000⟩, ⟨.privateRow 8 21, 20905587812959920890820⟩, ⟨.privateRow 8 22, 46456861806577601979600⟩, ⟨.privateRow 8 23, 94690341406261995869475⟩, ⟨.privateRow 8 24, 186126555941168694251400⟩, ⟨.privateRow 8 25, 438064067003274694382400⟩, ⟨.privateRow 8 26, 882867581191215153293760⟩, ⟨.privateRow 9 15, 23647183104090401856⟩, ⟨.privateRow 9 16, 152017605669152583360⟩, ⟨.privateRow 9 17, 886769366403390069600⟩, ⟨.privateRow 9 18, 3487959507853334273760⟩, ⟨.privateRow 9 19, 9270770648762714364000⟩, ⟨.privateRow 9 20, 20271547715981496991056⟩, ⟨.privateRow 9 21, 40535213037594963848160⟩, ⟨.privateRow 9 22, 77725334965257139600440⟩, ⟨.privateRow 9 23, 180571579267341743601120⟩, ⟨.privateRow 9 24, 372797841635985185259840⟩, ⟨.privateRow 9 25, 703349990656512867603936⟩, ⟨.privateRow 9 26, 558753377770776082854960⟩, ⟨.privateRow 10 13, 22169234160084751740⟩, ⟨.privateRow 10 14, 106412323968406808352⟩, ⟨.privateRow 10 15, 532061619842034041760⟩, ⟨.privateRow 10 16, 1882679577902581993920⟩, ⟨.privateRow 10 17, 4803334068018362877000⟩, ⟨.privateRow 10 18, 10270401570890172260640⟩, ⟨.privateRow 10 19, 20023252293388547771568⟩, ⟨.privateRow 10 20, 37106371487501855579040⟩, ⟨.privateRow 10 21, 82646904948795954486720⟩, ⟨.privateRow 10 22, 169727656729608859321440⟩, ⟨.privateRow 10 23, 324587147082520878475920⟩, ⟨.privateRow 10 24, 566007151187955813624288⟩, ⟨.privateRow 10 25, 605973846531756604061160⟩, ⟨.privateRow 10 26, 355239808181198061881760⟩, ⟨.privateRow 11 11, 13040725976520442200⟩, ⟨.privateRow 11 12, 83134628100317819025⟩, ⟨.privateRow 11 13, 369487236001412529000⟩, ⟨.privateRow 11 14, 1219307878804661345700⟩, ⟨.privateRow 11 15, 3018426497180770044600⟩, ⟨.privateRow 11 16, 6318231735624154245900⟩, ⟨.privateRow 11 17, 12031847994155087989800⟩, ⟨.privateRow 11 18, 21637172540242717698240⟩, ⟨.privateRow 11 19, 46013477123375906944800⟩, ⟨.privateRow 11 20, 92722821874554474152550⟩, ⟨.privateRow 11 21, 180457566063089879163600⟩, ⟨.privateRow 11 22, 328178563016454608257800⟩, ⟨.privateRow 11 23, 551481868966268284284240⟩, ⟨.privateRow 11 24, 711466147282519895215950⟩, ⟨.privateRow 11 27, 3422929754317085668656000⟩, ⟨.privateRow 12 9, 19354093314359703900⟩, ⟨.privateRow 12 10, 81970277566699922400⟩, ⟨.privateRow 12 11, 304826969701165336425⟩, ⟨.privateRow 12 12, 952221391066497431880⟩, ⟨.privateRow 12 13, 2339080420564044214200⟩, ⟨.privateRow 12 14, 4850433539860301177400⟩, ⟨.privateRow 12 15, 9086746811091880981050⟩, ⟨.privateRow 12 16, 15898507926232207676400⟩, ⟨.privateRow 12 17, 32154890632477212059460⟩, ⟨.privateRow 12 18, 62126639539094649519000⟩, ⟨.privateRow 12 19, 118926064893411790539525⟩, ⟨.privateRow 12 20, 219077276836657928317200⟩, ⟨.privateRow 12 21, 378856376628591203842500⟩, ⟨.privateRow 12 22, 609723614138262367784040⟩, ⟨.privateRow 12 24, 1691934837541325314938000⟩, ⟨.privateRow 13 7, 36670913648260491600⟩, ⟨.privateRow 13 8, 77416373257438815600⟩, ⟨.privateRow 13 9, 327881110266799689600⟩, ⟨.privateRow 13 10, 958027619060805343050⟩, ⟨.privateRow 13 12, 9306554013733537618200⟩, ⟨.privateRow 13 13, 6538705987435986117600⟩, ⟨.privateRow 13 14, 15212317345086727265400⟩, ⟨.privateRow 13 15, 29516751767427126602400⟩, ⟨.privateRow 13 16, 54485643498585438419280⟩, ⟨.privateRow 13 17, 100563868861413021464400⟩, ⟨.privateRow 13 18, 183070368660528439190100⟩, ⟨.privateRow 13 19, 320702855959887253538400⟩, ⟨.privateRow 13 20, 529411868520995340480600⟩, ⟨.privateRow 13 21, 813661566210333439719120⟩, ⟨.privateRow 13 23, 1679393385073620226810800⟩, ⟨.privateRow 14 6, 95344375485477278160⟩, ⟨.privateRow 14 7, 402565140938681841120⟩, ⟨.privateRow 14 8, 1172174969203808890320⟩, ⟨.privateRow 14 9, 1471878796557055481595⟩, ⟨.privateRow 14 10, 3743855810729741122416⟩, ⟨.privateRow 14 11, 19926974476464751135440⟩, ⟨.privateRow 14 12, 14352995601929156412240⟩, ⟨.privateRow 14 14, 138500706898403766156240⟩, ⟨.privateRow 14 16, 361906061703874975166880⟩, ⟨.privateRow 14 18, 1152659017119142877366880⟩, ⟨.privateRow 14 19, 685367152448105834506800⟩, ⟨.privateRow 15 4, 317020048489211949882⟩, ⟨.privateRow 15 5, 667410628398340947120⟩, ⟨.privateRow 15 6, 2113466989928079665880⟩, ⟨.privateRow 15 7, 3729647629284846469200⟩, ⟨.privateRow 15 8, 5547850848561209122935⟩, ⟨.privateRow 15 9, 15216962327482173594336⟩, ⟨.privateRow 15 10, 59780923429394253406320⟩, ⟨.privateRow 15 11, 46821422546098995674880⟩, ⟨.privateRow 15 13, 381000458275216543403640⟩, ⟨.privateRow 15 14, 69110370570648205074276⟩, ⟨.privateRow 15 16, 1986923153906135895885435⟩, ⟨.privateRow 15 17, 1197430011722109136411440⟩, ⟨.privateRow 15 18, 2743280152926647406312240⟩, ⟨.privateRow 16 2, 1509619278520056904200⟩, ⟨.privateRow 16 3, 1585100242446059749410⟩, ⟨.privateRow 16 4, 5005579712987557103400⟩, ⟨.privateRow 16 5, 10567334949640398329400⟩, ⟨.privateRow 16 6, 18648238146424232346000⟩, ⟨.privateRow 16 9, 58875151862282219263800⟩, ⟨.privateRow 16 11, 7925501212230298747050⟩, ⟨.privateRow 16 12, 14410002204055088631000⟩, ⟨.privateRow 16 13, 82425212607195106969320⟩, ⟨.privateRow 16 15, 118882518183454481205750⟩, ⟨.privateRow 16 17, 14017569810697988383949100⟩, ⟨.privateRow 16 20, 42396147817957278097552800⟩, ⟨.privateRow 17 6, 459679070309357327328900⟩, ⟨.privateRow 17 7, 202892831033095647924480⟩, ⟨.privateRow 17 12, 304339246549643471886720⟩, ⟨.privateRow 17 14, 190212029093527169929200⟩, ⟨.privateRow 17 16, 41466222342388923044565600⟩, ⟨.privateRow 17 18, 123637818910792660453980000⟩, ⟨.privateRow 17 21, 503427837000868576412616000⟩, ⟨.privateRow 18 5, 7545077154043244407191600⟩, ⟨.privateRow 18 9, 9341524095482112123189600⟩, ⟨.privateRow 18 12, 4311472659453282518395200⟩, ⟨.privateRow 18 13, 4850406741884942833194600⟩, ⟨.privateRow 18 14, 6775171321998015386049600⟩, ⟨.privateRow 18 15, 255814044460894762758115200⟩, ⟨.privateRow 18 16, 424248909690202999810087680⟩, ⟨.privateRow 18 20, 7105306942779009590315289600⟩, ⟨.hall 16 6, 414688549348599926400⟩, ⟨.hall 14 10, 562511864204600310⟩, ⟨.hall 9 17, 61750638779483808⟩, ⟨.hall 12 17, 1265475432981929400⟩, ⟨.hall 14 19, 108149602463146369125⟩, ⟨.hall 6 23, 1378683132204221844⟩, ⟨.hall 8 24, 13310065568903731936⟩, ⟨.hall 5 25, 5573426962884806025⟩, ⟨.hall 9 28, 330245143350228025920⟩, ⟨.hall 4 29, 546923840769468468306⟩, ⟨.hall 3 34, 81212384478832093252485720⟩]
  caps := #[0, 0, 280949702372177758920000, 0, 3900155985092051757072, 8843392499154117913008, 0, 88948348512271728480, 2327578617795544459605, 315521074147344445044, 2030047876869260940972, 615176235950274449850, 606541145440441256265, 0, 46073895965822107583343, 154471433851282774777551, 11918777410385615780010, 2484189548180909681112000, 0] }

theorem case_56_38_24_checked :
    (Witness.linear .conditional case_56_38_24).check 56 38 24 = true := by
  change case_56_38_24.check 56 38 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_39_1_checked :
    (Witness.rising).check 56 39 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_39_2_checked :
    (Witness.rising).check 56 39 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_39_3_checked :
    (Witness.rising).check 56 39 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_39_4_checked :
    (Witness.rising).check 56 39 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_39_5_checked :
    (Witness.rising).check 56 39 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_39_6_checked :
    (Witness.rising).check 56 39 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_39_7_checked :
    (Witness.rising).check 56 39 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_39_8_checked :
    (Witness.rising).check 56 39 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_39_9_checked :
    (Witness.rising).check 56 39 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_39_10_checked :
    (Witness.rising).check 56 39 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_39_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_39_11_checked :
    (Witness.linear .positive case_56_39_11).check 56 39 11 = true := by
  change case_56_39_11.check 56 39 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_39_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_56_39_12_checked :
    (Witness.linear .positive case_56_39_12).check 56 39 12 = true := by
  change case_56_39_12.check 56 39 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_39_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_56_39_13_checked :
    (Witness.linear .positive case_56_39_13).check 56 39 13 = true := by
  change case_56_39_13.check 56 39 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_39_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_56_39_14_checked :
    (Witness.linear .positive case_56_39_14).check 56 39 14 = true := by
  change case_56_39_14.check 56 39 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_39_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_56_39_15_checked :
    (Witness.linear .positive case_56_39_15).check 56 39 15 = true := by
  change case_56_39_15.check 56 39 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_39_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_56_39_16_checked :
    (Witness.linear .positive case_56_39_16).check 56 39 16 = true := by
  change case_56_39_16.check 56 39 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_39_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_56_39_17_checked :
    (Witness.linear .positive case_56_39_17).check 56 39 17 = true := by
  change case_56_39_17.check 56 39 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_39_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_56_39_18_checked :
    (Witness.linear .positive case_56_39_18).check 56 39 18 = true := by
  change case_56_39_18.check 56 39 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_39_19 : Certificate := {
  objectiveScale := 80134312258000000
  eta := 378461985041155364027078400
  rows := #[⟨.count 2, 39569411442441887501695200⟩, ⟨.count 3, 4066209324325173591165600⟩, ⟨.count 4, 379751707822439119527360⟩, ⟨.count 5, 31495061814011123328000⟩, ⟨.count 6, 2558973772388403770400⟩, ⟨.count 7, 250528900793270299200⟩, ⟨.count 8, 100211560317308119680⟩, ⟨.path 6, 1220975938395467654400⟩, ⟨.privateRow 2 36, 456776818371330073016400⟩, ⟨.privateRow 2 37, 2910832666091809288830000⟩, ⟨.privateRow 3 33, 343627528068889486301880⟩, ⟨.privateRow 3 34, 621773760606551262790080⟩, ⟨.privateRow 3 35, 914747824503108067792320⟩, ⟨.privateRow 3 36, 1446161377902433250778720⟩, ⟨.privateRow 4 29, 20069665729160480999280⟩, ⟨.privateRow 4 30, 60605028842732029295640⟩, ⟨.privateRow 4 31, 158042220182707816859904⟩, ⟨.privateRow 4 32, 222950589919339678496100⟩, ⟨.privateRow 4 33, 309550527333250576092720⟩, ⟨.privateRow 4 34, 463430150179539922819440⟩, ⟨.privateRow 5 26, 5800340550747048546240⟩, ⟨.privateRow 5 27, 12785026655125140375960⟩, ⟨.privateRow 5 28, 32642381922950099963520⟩, ⟨.privateRow 5 29, 56953570113670114684800⟩, ⟨.privateRow 5 30, 81398987258311748241216⟩, ⟨.privateRow 5 31, 109248495667351084044000⟩, ⟨.privateRow 5 32, 164719173287278175005440⟩, ⟨.privateRow 5 33, 155467498879412407527840⟩, ⟨.privateRow 6 23, 984220681687847604000⟩, ⟨.privateRow 6 24, 2837836298866627258200⟩, ⟨.privateRow 6 25, 7228554117729636291600⟩, ⟨.privateRow 6 26, 13799594141165029947750⟩, ⟨.privateRow 6 27, 21920000610733634494800⟩, ⟨.privateRow 6 28, 31423979209222556556600⟩, ⟨.privateRow 6 29, 41422567756635879493680⟩, ⟨.privateRow 6 30, 61161113527885663191900⟩, ⟨.privateRow 6 31, 61054489620702813034800⟩, ⟨.privateRow 6 32, 17010614115171632755800⟩, ⟨.privateRow 7 20, 94980737113932146400⟩, ⟨.privateRow 7 21, 524917696900185388800⟩, ⟨.privateRow 7 22, 1719539273626537053600⟩, ⟨.privateRow 7 23, 3544983946224774733680⟩, ⟨.privateRow 7 24, 6143923043263533528000⟩, ⟨.privateRow 7 25, 9410491836047215613700⟩, ⟨.privateRow 7 26, 13270362489978225746400⟩, ⟨.privateRow 7 27, 17361056327590790614800⟩, ⟨.privateRow 7 28, 25296261011526206782080⟩, ⟨.privateRow 7 29, 13653825093233231306400⟩, ⟨.privateRow 8 18, 54579510529962458040⟩, ⟨.privateRow 8 19, 366157624236318129600⟩, ⟨.privateRow 8 20, 993764639813305520160⟩, ⟨.privateRow 8 21, 1877827988218648742640⟩, ⟨.privateRow 8 22, 3087768702277056437640⟩, ⟨.privateRow 8 23, 4615299083502690623040⟩, ⟨.privateRow 8 24, 6260090908571841601260⟩, ⟨.privateRow 8 25, 8594930789357694621840⟩, ⟨.privateRow 8 26, 5294510770097778989760⟩, ⟨.privateRow 9 16, 40084624126923247872⟩, ⟨.privateRow 9 17, 260072858918728215360⟩, ⟨.privateRow 9 18, 636386233468033614720⟩, ⟨.privateRow 9 19, 1147793519560279111520⟩, ⟨.privateRow 9 20, 1825065083354611512960⟩, ⟨.privateRow 9 21, 2673421736909519948352⟩, ⟨.privateRow 9 22, 3652154642675229250560⟩, ⟨.privateRow 10 14, 33664821044095696455⟩, ⟨.privateRow 10 15, 205433698650481645344⟩, ⟨.privateRow 10 16, 476899657581475248120⟩, ⟨.privateRow 10 17, 843126108438890430000⟩, ⟨.privateRow 10 18, 1314232858744697111220⟩, ⟨.privateRow 10 19, 456645860082279045360⟩, ⟨.privateRow 11 12, 32631915649543610400⟩, ⟨.privateRow 11 13, 186778243002125624850⟩, ⟨.privateRow 11 14, 433057099942652945760⟩, ⟨.privateRow 11 15, 398801107385205782400⟩, ⟨.privateRow 12 10, 38275248732305184600⟩, ⟨.privateRow 12 11, 204563514233160482400⟩, ⟨.privateRow 12 12, 77917470633621268650⟩, ⟨.privateRow 13 8, 53873132050282184640⟩, ⟨.privateRow 13 9, 39368827267513904160⟩, ⟨.privateRow 14 6, 25589737723884037704⟩, ⟨.hall 4 34, 43751140154206309034496⟩, ⟨.hall 3 35, 191468104258483455443040⟩, ⟨.assumptionRow 19, 91139581600867800⟩]
  caps := #[0, 29135919741178476626400, 23594686185328336478400, 0, 566048110295244165732, 184743190803887716000, 502464974122671438450, 132789383301989867160, 39547559737807823940, 118688851696792734952, 12722700852506645000, 202380794051465300700, 16950449406928387350, 375563595746339000, 91139581600867800, 1770538925229859184400, 429321583165554679600, 85847642191140629800] }

theorem case_56_39_19_checked :
    (Witness.linear .conditional case_56_39_19).check 56 39 19 = true := by
  change case_56_39_19.check 56 39 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_39_20 : Certificate := {
  objectiveScale := 16173990582750000
  eta := 104022165276964911014438400
  rows := #[⟨.count 2, 9326258144888537189937600⟩, ⟨.count 3, 772581825648244086995520⟩, ⟨.count 4, 53072533304573934191040⟩, ⟨.count 5, 2966524352930669731200⟩, ⟨.count 6, 211894596637904980800⟩, ⟨.count 7, 89894677361535446400⟩, ⟨.count 8, 35957870944614178560⟩, ⟨.count 9, 17978935472307089280⟩, ⟨.path 5, 1997392254081121497600⟩, ⟨.privateRow 2 36, 42581984982692321766600⟩, ⟨.privateRow 2 37, 657208749355515456699600⟩, ⟨.privateRow 3 33, 69470232103838919913560⟩, ⟨.privateRow 3 34, 129049302916100671584480⟩, ⟨.privateRow 3 35, 206214644255805583398000⟩, ⟨.privateRow 3 36, 341941373747808531016320⟩, ⟨.privateRow 4 29, 3843364374256095580320⟩, ⟨.privateRow 4 30, 11056777771786236289800⟩, ⟨.privateRow 4 31, 31448689717675730900400⟩, ⟨.privateRow 4 32, 47230422696436362282900⟩, ⟨.privateRow 4 33, 69982899308482295575440⟩, ⟨.privateRow 4 34, 111585460377826078764120⟩, ⟨.privateRow 5 26, 900944433112277473920⟩, ⟨.privateRow 5 27, 2131306484516260931880⟩, ⟨.privateRow 5 28, 5878561523868735324480⟩, ⟨.privateRow 5 29, 11275146925543632811680⟩, ⟨.privateRow 5 30, 17321676959826605830464⟩, ⟨.privateRow 5 31, 25035346592768473481520⟩, ⟨.privateRow 5 32, 40655509941592702316160⟩, ⟨.privateRow 5 33, 42908655819175758612000⟩, ⟨.privateRow 6 22, 490496751476631900⟩, ⟨.privateRow 6 23, 103806948857963551200⟩, ⟨.privateRow 6 24, 403776925815563380080⟩, ⟨.privateRow 6 25, 1169344255520290449600⟩, ⟨.privateRow 6 26, 2471367882315009828150⟩, ⟨.privateRow 6 27, 4306000910248854788400⟩, ⟨.privateRow 6 28, 6690375690141259116000⟩, ⟨.privateRow 6 29, 9565863845997865966560⟩, ⟨.privateRow 6 30, 15384430610064559543500⟩, ⟨.privateRow 6 31, 17463646339574002167600⟩, ⟨.privateRow 6 32, 12760763486416055510400⟩, ⟨.privateRow 7 21, 51368387063734540800⟩, ⟨.privateRow 7 22, 235827595156235846400⟩, ⟨.privateRow 7 23, 563768048024486585280⟩, ⟨.privateRow 7 24, 1086227351451886644000⟩, ⟨.privateRow 7 25, 1823577740762576198400⟩, ⟨.privateRow 7 26, 2802787619165015882400⟩, ⟨.privateRow 7 27, 3993892094205360547200⟩, ⟨.privateRow 7 28, 6385732616860500103200⟩, ⟨.privateRow 7 29, 7562389733039169428400⟩, ⟨.privateRow 7 30, 1765788305315874840000⟩, ⟨.privateRow 8 19, 30253016419747506000⟩, ⟨.privateRow 8 20, 133343771419610912160⟩, ⟨.privateRow 8 21, 291749089255165039680⟩, ⟨.privateRow 8 22, 533749646834116713000⟩, ⟨.privateRow 8 23, 874475444778047592480⟩, ⟨.privateRow 8 24, 1323980045015364246510⟩, ⟨.privateRow 8 25, 1873340865730569034800⟩, ⟨.privateRow 8 26, 2990870828049418914600⟩, ⟨.privateRow 8 27, 1645971542489714023584⟩, ⟨.privateRow 9 17, 19405835112966382080⟩, ⟨.privateRow 9 18, 81904039373843406720⟩, ⟨.privateRow 9 19, 172464603234353189760⟩, ⟨.privateRow 9 20, 305278692211598152320⟩, ⟨.privateRow 9 21, 489826108645522032384⟩, ⟨.privateRow 9 22, 731587300206471188480⟩, ⟨.privateRow 9 23, 1027546103729773227600⟩, ⟨.privateRow 9 24, 630404261243275559040⟩, ⟨.privateRow 10 15, 14083499453307219936⟩, ⟨.privateRow 10 16, 57468383027553017520⟩, ⟨.privateRow 10 17, 121184940058531438320⟩, ⟨.privateRow 10 18, 210503369488262170320⟩, ⟨.privateRow 10 19, 332406000152768571120⟩, ⟨.privateRow 10 20, 451720753741715618160⟩, ⟨.privateRow 11 13, 11838807956095069950⟩, ⟨.privateRow 11 14, 47515758033954450240⟩, ⟨.privateRow 11 15, 103424743597072669200⟩, ⟨.privateRow 11 16, 180283281521760648000⟩, ⟨.privateRow 11 17, 60732415955561149800⟩, ⟨.privateRow 12 11, 11771922035439165600⟩, ⟨.privateRow 12 12, 47455560705364136325⟩, ⟨.privateRow 12 13, 74555506224448048800⟩, ⟨.privateRow 13 9, 14126306442526998720⟩, ⟨.privateRow 13 10, 29083572087555585600⟩, ⟨.privateRow 14 7, 12081709457424406800⟩, ⟨.hall 4 34, 14979938960411130214080⟩, ⟨.hall 3 35, 50669884017140800492080⟩, ⟨.assumptionRow 20, 15110245193223180⟩]
  caps := #[0, 5829153008986493386200, 0, 0, 214816256134089023700, 60854003265752384688, 0, 17326382604061662180, 0, 13213567816772313172, 16917925103733242484, 1263207354457448400, 51817926418858474875, 74487480576589080, 15110245193223180, 1007810744477044467960, 293976945559910492880, 73625484657452107380] }

theorem case_56_39_20_checked :
    (Witness.linear .conditional case_56_39_20).check 56 39 20 = true := by
  change case_56_39_20.check 56 39 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_39_21 : Certificate := {
  objectiveScale := 1476874320516094500000
  eta := 4796591014522461511649878185600
  rows := #[⟨.count 2, 473127708838648644623053411200⟩, ⟨.count 3, 41976145211779096921944300960⟩, ⟨.count 4, 3208802642917241889939900480⟩, ⟨.count 5, 205692477110079608329480800⟩, ⟨.count 6, 10941089207982957889866000⟩, ⟨.count 7, 1392502262834194640528400⟩, ⟨.count 8, 1114001810267355712422720⟩, ⟨.path 5, 77474702556285962274547200⟩, ⟨.path 6, 3966666849061581240576000⟩, ⟨.privateRow 2 36, 39576654937576354427117788500⟩, ⟨.privateRow 2 37, 69495610431266151924850858800⟩, ⟨.privateRow 3 32, 1967382897022663555924144656⟩, ⟨.privateRow 3 33, 6597768554792603153132927760⟩, ⟨.privateRow 3 34, 15093889027764969386543538960⟩, ⟨.privateRow 3 35, 21207113211833367277927267800⟩, ⟨.privateRow 3 36, 36599693974976271414864148560⟩, ⟨.privateRow 4 29, 533174907232449513627298560⟩, ⟨.privateRow 4 30, 1108952331823792668523851540⟩, ⟨.privateRow 4 31, 2932868373091911691957479960⟩, ⟨.privateRow 4 32, 4794002352815852743813135890⟩, ⟨.privateRow 4 33, 7354454284416704520796060320⟩, ⟨.privateRow 4 34, 11991762004625561336029831980⟩, ⟨.privateRow 5 26, 87236951284984117575198240⟩, ⟨.privateRow 5 27, 205254833541760290013886160⟩, ⟨.privateRow 5 28, 540677368403637827608920960⟩, ⟨.privateRow 5 29, 1039841118326700317852864640⟩, ⟨.privateRow 5 30, 1695431183669039154613635360⟩, ⟨.privateRow 5 31, 2595007538349397952318417880⟩, ⟨.privateRow 5 32, 4455503287869539998297164960⟩, ⟨.privateRow 5 33, 5031588104967202674391576080⟩, ⟨.privateRow 6 23, 9482277313585230171217200⟩, ⟨.privateRow 6 24, 34391490410426430967145460⟩, ⟨.privateRow 6 25, 103697212160105145333952200⟩, ⟨.privateRow 6 26, 218685020544559370823696675⟩, ⟨.privateRow 6 27, 393306106814587376717135400⟩, ⟨.privateRow 6 28, 643761532231930594508726700⟩, ⟨.privateRow 6 29, 979081602925034958371142120⟩, ⟨.privateRow 6 30, 1684380683568976367144870700⟩, ⟨.privateRow 6 31, 2089748038724744956964406000⟩, ⟨.privateRow 6 32, 1822056056102761920592351200⟩, ⟨.privateRow 7 20, 413160012049706102134800⟩, ⟨.privateRow 7 21, 4177506788502583921585200⟩, ⟨.privateRow 7 22, 19006751665438163210329200⟩, ⟨.privateRow 7 23, 47802613394150996016996360⟩, ⟨.privateRow 7 24, 93761819030835772462245600⟩, ⟨.privateRow 7 25, 163892543113217444209333650⟩, ⟨.privateRow 7 26, 265513237584895520948098800⟩, ⟨.privateRow 7 27, 402333689511736951495527000⟩, ⟨.privateRow 7 28, 691635981060275418027020160⟩, ⟨.privateRow 7 29, 900750035159033333187513600⟩, ⟨.privateRow 7 30, 682922895472827171561999600⟩, ⟨.privateRow 8 18, 49732223672649808590300⟩, ⟨.privateRow 8 19, 2645754299384969817003960⟩, ⟨.privateRow 8 20, 10385746043638368360607650⟩, ⟨.privateRow 8 21, 23913061586307215235983160⟩, ⟨.privateRow 8 22, 45089223270571222460309592⟩, ⟨.privateRow 8 23, 76989902887366139236325760⟩, ⟨.privateRow 8 24, 122836105860261394727611485⟩, ⟨.privateRow 8 25, 184586121383407029563757480⟩, ⟨.privateRow 8 26, 316747848052684807565526720⟩, ⟨.privateRow 8 27, 431982051976423861384720248⟩, ⟨.privateRow 8 28, 47310264379791762911952390⟩, ⟨.privateRow 9 17, 1724050420651860031130400⟩, ⟨.privateRow 9 18, 6284112775867134788025600⟩, ⟨.privateRow 9 19, 13770300154693702556336400⟩, ⟨.privateRow 9 20, 25239455155855342050143040⟩, ⟨.privateRow 9 21, 42146401821781624453326240⟩, ⟨.privateRow 9 22, 66069934524992306697268480⟩, ⟨.privateRow 9 23, 98155937282445897772357440⟩, ⟨.privateRow 9 24, 167011858698018646092580800⟩, ⟨.privateRow 9 25, 60135468091284109290967200⟩, ⟨.privateRow 10 15, 1253252036550775176475560⟩, ⟨.privateRow 10 16, 4406275017396773041100580⟩, ⟨.privateRow 10 17, 9479726943140478898981800⟩, ⟨.privateRow 10 18, 17034944348671647769130760⟩, ⟨.privateRow 10 19, 27900681702605136252041760⟩, ⟨.privateRow 10 20, 42972619831063246606706424⟩, ⟨.privateRow 10 21, 63033935764294544061252240⟩, ⟨.privateRow 10 22, 8859795647282563400361945⟩, ⟨.privateRow 11 13, 1056809753043808432543875⟩, ⟨.privateRow 11 14, 3686815514932439143494240⟩, ⟨.privateRow 11 15, 7999783407914812067525400⟩, ⟨.privateRow 11 16, 14292275972386129607181600⟩, ⟨.privateRow 11 17, 23092329192000394455429300⟩, ⟨.privateRow 11 18, 12351675915789025188063600⟩, ⟨.privateRow 12 11, 1051202688610127326673400⟩, ⟨.privateRow 12 12, 3783793351094106270245325⟩, ⟨.privateRow 12 13, 8436795455933525306185560⟩, ⟨.privateRow 12 14, 8700770941586447464798200⟩, ⟨.privateRow 13 9, 1264303641811364022828960⟩, ⟨.privateRow 13 10, 4839822990825402548928960⟩, ⟨.privateRow 13 11, 1477047043077699315131910⟩, ⟨.privateRow 14 7, 1946362185420126193039320⟩, ⟨.privateRow 14 8, 632151820905682011414480⟩, ⟨.privateRow 15 5, 663759411950966111985204⟩, ⟨.hall 5 33, 204019134054741038299266000⟩, ⟨.hall 4 34, 1977298649870584110903188928⟩, ⟨.hall 3 35, 5818957511436802915070288400⟩, ⟨.assumptionRow 21, 1014230780691680617065⟩]
  caps := #[0, 718514733852479282412944250, 431686714939255503887058900, 7311874900183798561178562, 5833162531806882087803130, 8422917778737352868221530, 898403975112080483378640, 3554855373517717796571420, 130634997637096795190985, 406043998248796286529150, 121034369801714723524170, 1423969695937019413228500, 99321826171333778137125, 1676266907451392800428885, 0, 29133000910283556091481676, 74243850045622598441490390, 22231489943401145731949625] }

theorem case_56_39_21_checked :
    (Witness.linear .conditional case_56_39_21).check 56 39 21 = true := by
  change case_56_39_21.check 56 39 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_39_22 : Certificate := {
  objectiveScale := 642906139487040000
  eta := 2539464156347714580054470400
  rows := #[⟨.count 2, 281213304769078855540567200⟩, ⟨.count 3, 28825304161691935431293760⟩, ⟨.count 4, 2600940942255573592234560⟩, ⟨.count 5, 193694630156168408467200⟩, ⟨.count 6, 8857986135190628436000⟩, ⟨.path 6, 8980640635772264659200⟩, ⟨.privateRow 2 36, 23282183124632794604041800⟩, ⟨.privateRow 2 37, 42775805579244557426006400⟩, ⟨.privateRow 3 32, 849784010334741124074432⟩, ⟨.privateRow 3 33, 3962314989166204398087360⟩, ⟨.privateRow 3 34, 9140313118468393147366080⟩, ⟨.privateRow 3 35, 13124720581202884098004560⟩, ⟨.privateRow 3 36, 22967813196694879200848160⟩, ⟨.privateRow 4 29, 261234665392679047761120⟩, ⟨.privateRow 4 30, 644477544576019489575240⟩, ⟨.privateRow 4 31, 1765998979800685210028448⟩, ⟨.privateRow 4 32, 2914159331995914213731520⟩, ⟨.privateRow 4 33, 4537316395821878725296240⟩, ⟨.privateRow 4 34, 7538736733456237507598400⟩, ⟨.privateRow 5 26, 51074491908388038330240⟩, ⟨.privateRow 5 27, 116423464436855493077160⟩, ⟨.privateRow 5 28, 319359926794072790545920⟩, ⟨.privateRow 5 29, 622618003235732394290400⟩, ⟨.privateRow 5 30, 1023510771300826480351680⟩, ⟨.privateRow 5 31, 1591248629325644492243040⟩, ⟨.privateRow 5 32, 2794950523029882111935040⟩, ⟨.privateRow 5 33, 3261982920904399556985120⟩, ⟨.privateRow 6 22, 492110340843923802000⟩, ⟨.privateRow 6 23, 7301127965975305862400⟩, ⟨.privateRow 6 24, 21318219965358779102640⟩, ⟨.privateRow 6 25, 60288984646056709342800⟩, ⟨.privateRow 6 26, 128846789991460349458650⟩, ⟨.privateRow 6 27, 232655708855554490048400⟩, ⟨.privateRow 6 28, 384387387233188881742200⟩, ⟨.privateRow 6 29, 594488976153093709768080⟩, ⟨.privateRow 6 30, 1049843595639384842996700⟩, ⟨.privateRow 6 31, 1354090813866140733583200⟩, ⟨.privateRow 6 32, 1255816378799609150323800⟩, ⟨.privateRow 7 18, 3578984297046718560⟩, ⟨.privateRow 7 19, 138046537171802001600⟩, ⟨.privateRow 7 20, 1015880927392491652800⟩, ⟨.privateRow 7 21, 3422403734050924623000⟩, ⟨.privateRow 7 22, 11981463339885946452000⟩, ⟨.privateRow 7 23, 27926814469855544923680⟩, ⟨.privateRow 7 24, 54722669901844326782400⟩, ⟨.privateRow 7 25, 95753488002299300873700⟩, ⟨.privateRow 7 26, 156498757640432869147200⟩, ⟨.privateRow 7 27, 241304068767632382111600⟩, ⟨.privateRow 7 28, 426536190553433824543680⟩, ⟨.privateRow 7 29, 578976763463618969849400⟩, ⟨.privateRow 7 30, 575518569886597578040800⟩, ⟨.privateRow 8 16, 28184501339242908660⟩, ⟨.privateRow 8 17, 162843785515625694480⟩, ⟨.privateRow 8 18, 552953073893718017520⟩, ⟨.privateRow 8 19, 2240306516709051714000⟩, ⟨.privateRow 8 20, 6595173313382840626440⟩, ⟨.privateRow 8 21, 14044422424924557272880⟩, ⟨.privateRow 8 22, 26087574439603236255696⟩, ⟨.privateRow 8 23, 44477230854165253784640⟩, ⟨.privateRow 8 24, 71466500562540268725540⟩, ⟨.privateRow 8 25, 109135757661994112409360⟩, ⟨.privateRow 8 26, 192543986704667888450160⟩, ⟨.privateRow 8 27, 273532464464108378072544⟩, ⟨.privateRow 8 28, 131771938594740345621720⟩, ⟨.privateRow 9 13, 7423078542022823680⟩, ⟨.privateRow 9 14, 33403853439102706560⟩, ⟨.privateRow 9 15, 108562523677083796320⟩, ⟨.privateRow 9 16, 438703941833548879488⟩, ⟨.privateRow 9 17, 1534191268667360022720⟩, ⟨.privateRow 9 18, 4070131065195283630080⟩, ⟨.privateRow 9 19, 8172809474767128871680⟩, ⟨.privateRow 9 20, 14567116813397789397120⟩, ⟨.privateRow 9 21, 24154326421815167113536⟩, ⟨.privateRow 9 22, 38009873674427868653440⟩, ⟨.privateRow 9 23, 57204099014463384984000⟩, ⟨.privateRow 9 24, 99743906369160681788160⟩, ⟨.privateRow 9 25, 90886317898891947432000⟩, ⟨.privateRow 10 10, 1878966755949527244⟩, ⟨.privateRow 10 11, 9889298715523827600⟩, ⟨.privateRow 10 12, 29228371759214868240⟩, ⟨.privateRow 10 13, 108316907107678629360⟩, ⟨.privateRow 10 14, 382839476524716175965⟩, ⟨.privateRow 10 15, 1215065168847360951120⟩, ⟨.privateRow 10 16, 2966083236177468006600⟩, ⟨.privateRow 10 17, 5740966118947324779360⟩, ⟨.privateRow 10 18, 9899023192594092697140⟩, ⟨.privateRow 10 19, 15957552212800439557680⟩, ⟨.privateRow 10 20, 24539305832700825806640⟩, ⟨.privateRow 10 21, 36280760316545427162480⟩, ⟨.privateRow 10 22, 30505025282840574806340⟩, ⟨.privateRow 11 8, 2556417355033370400⟩, ⟨.privateRow 11 9, 10736952891140155680⟩, ⟨.privateRow 11 10, 36731680943374216800⟩, ⟨.privateRow 11 11, 125264450396635149600⟩, ⟨.privateRow 11 12, 397898842436370475200⟩, ⟨.privateRow 11 13, 1150867138019085436950⟩, ⟨.privateRow 11 14, 2648448379814571734400⟩, ⟨.privateRow 11 15, 5011856224542922669200⟩, ⟨.privateRow 11 16, 8445026408608314756000⟩, ⟨.privateRow 11 17, 13295926663528559450400⟩, ⟨.privateRow 11 18, 15280636137345376106400⟩, ⟨.privateRow 12 6, 4473730371308398200⟩, ⟨.privateRow 12 7, 18747060603578049600⟩, ⟨.privateRow 12 8, 54132137492831618220⟩, ⟨.privateRow 12 9, 170943592082626162800⟩, ⟨.privateRow 12 10, 508514018872054595400⟩, ⟨.privateRow 12 11, 1348961287254520539600⟩, ⟨.privateRow 12 12, 2977267562105739002100⟩, ⟨.privateRow 12 13, 5557566115930712803920⟩, ⟨.privateRow 12 14, 6123258669643680450600⟩, ⟨.privateRow 13 4, 10270128852394931520⟩, ⟨.privateRow 13 5, 32210858673420467040⟩, ⟨.privateRow 13 6, 101234127259321467840⟩, ⟨.privateRow 13 7, 295266204506354281200⟩, ⟨.privateRow 13 8, 808096980754232769600⟩, ⟨.privateRow 13 9, 2020933133065713746880⟩, ⟨.privateRow 13 10, 2653922120504172598080⟩, ⟨.privateRow 14 2, 31987172154855047130⟩, ⟨.privateRow 14 3, 100133756310850582320⟩, ⟨.privateRow 14 4, 244265678273438541720⟩, ⟨.privateRow 14 5, 658021827185589540960⟩, ⟨.privateRow 14 6, 959615164645651413900⟩, ⟨.privateRow 15 1, 597093880223960879760⟩, ⟨.hall 5 33, 199530479845235175436800⟩, ⟨.hall 4 34, 1344996614767345021722240⟩, ⟨.hall 3 35, 3759601616830169679408840⟩, ⟨.assumptionRow 22, 168285155674405770⟩]
  caps := #[0, 602111671057956559500, 0, 2705502479174283428640, 0, 1359365620526647776900, 437007123575774424420, 1713086039954640780, 52021845547090202916, 419690601318120468982, 0, 81742755169311663600, 2139610177582277400, 4427376170879328574050, 5509434166831903805640, 8138295549777623681880, 81388239968849878890540, 27838250132523280820370] }

theorem case_56_39_22_checked :
    (Witness.linear .conditional case_56_39_22).check 56 39 22 = true := by
  change case_56_39_22.check 56 39 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_39_23 : Certificate := {
  objectiveScale := 62787590545680000000
  eta := 368555481055583584278804288000
  rows := #[⟨.count 2, 39995109524347560410920092000⟩, ⟨.count 3, 4115827825771784740273656000⟩, ⟨.count 4, 371532284065527566616835200⟩, ⟨.count 5, 26656632942833664506736000⟩, ⟨.count 6, 1201733452340861924484000⟩, ⟨.path 6, 1224999327514615484832000⟩, ⟨.privateRow 2 37, 11164431517733609331708492000⟩, ⟨.privateRow 3 34, 1899952726872643519396320000⟩, ⟨.privateRow 3 35, 1077670860661018033443633600⟩, ⟨.privateRow 4 29, 9393809934596945355154800⟩, ⟨.privateRow 4 30, 62797856117854525626558600⟩, ⟨.privateRow 4 31, 140233554008525198500559280⟩, ⟨.privateRow 4 32, 423832270153880214325799100⟩, ⟨.privateRow 4 33, 669307267089504171359431200⟩, ⟨.privateRow 4 34, 924925076443711115287515000⟩, ⟨.privateRow 5 26, 2641385850801732876441600⟩, ⟨.privateRow 5 27, 8898289972105745795383800⟩, ⟨.privateRow 5 28, 32506109539422691120977600⟩, ⟨.privateRow 5 29, 61812798848587243352095200⟩, ⟨.privateRow 5 30, 126841873409621302618445760⟩, ⟨.privateRow 6 23, 470099587417086482856000⟩, ⟨.privateRow 6 24, 1414768018892196538369800⟩, ⟨.privateRow 6 25, 5003176477506652422978000⟩, ⟨.privateRow 6 26, 13157615696936596184549250⟩, ⟨.privateRow 6 27, 24456056101534164099564000⟩, ⟨.privateRow 6 28, 44943617245374154296990000⟩, ⟨.privateRow 6 29, 78451344738724813451996400⟩, ⟨.privateRow 6 30, 82801255674546509115015000⟩, ⟨.privateRow 6 31, 128682589174398760216716000⟩, ⟨.privateRow 6 32, 150316825996969479054207000⟩, ⟨.privateRow 7 18, 662112094953642933600⟩, ⟨.privateRow 7 19, 3547029080108801430000⟩, ⟨.privateRow 7 20, 59590088545827864024000⟩, ⟨.privateRow 7 21, 231739233233775026760000⟩, ⟨.privateRow 7 22, 836969880030036817428000⟩, ⟨.privateRow 7 23, 2366719683411796666153200⟩, ⟨.privateRow 7 24, 5442561420518944914192000⟩, ⟨.privateRow 7 25, 10104244389051937193569500⟩, ⟨.privateRow 7 26, 17752171140128529396864000⟩, ⟨.privateRow 7 27, 30122789759915985264132000⟩, ⟨.privateRow 7 28, 60434281466893758764340000⟩, ⟨.privateRow 7 29, 69916554306748617627159000⟩, ⟨.privateRow 7 30, 96231371880562463969424000⟩, ⟨.privateRow 7 31, 96908381497652563869030000⟩, ⟨.privateRow 8 15, 408951588059602988400⟩, ⟨.privateRow 8 16, 869022124626656350350⟩, ⟨.privateRow 8 17, 7879133929948350909840⟩, ⟨.privateRow 8 18, 33271132771420557413400⟩, ⟨.privateRow 8 19, 152947893934291517661600⟩, ⟨.privateRow 8 20, 466954554966056678921400⟩, ⟨.privateRow 8 21, 1176181944676514522182800⟩, ⟨.privateRow 8 22, 2495136324228055713124920⟩, ⟨.privateRow 8 23, 4590754210361083280115600⟩, ⟨.privateRow 8 24, 7868995338494373252419250⟩, ⟨.privateRow 8 25, 12980707621566169713228000⟩, ⟨.privateRow 8 26, 25536504806195839073818200⟩, ⟨.privateRow 8 27, 42348490959606515940175920⟩, ⟨.privateRow 8 28, 50849960600404169684379900⟩, ⟨.privateRow 8 30, 140392262277685586711743200⟩, ⟨.privateRow 9 13, 343317382568555595200⟩, ⟨.privateRow 9 14, 1454050090878588403200⟩, ⟨.privateRow 9 15, 5407248775454750624400⟩, ⟨.privateRow 9 16, 26366774981265069711360⟩, ⟨.privateRow 9 17, 105055119065978012131200⟩, ⟨.privateRow 9 18, 288545055534156802550400⟩, ⟨.privateRow 9 19, 664834111344007910104800⟩, ⟨.privateRow 9 20, 1332009023023710517449600⟩, ⟨.privateRow 9 21, 2399582513724662477090880⟩, ⟨.privateRow 9 22, 4033292610415391132409600⟩, ⟨.privateRow 9 23, 6485608674102583748923200⟩, ⟨.privateRow 9 24, 12376199278873493714851200⟩, ⟨.privateRow 9 25, 20755595680564597063411200⟩, ⟨.privateRow 9 26, 31547434284224573642928000⟩, ⟨.privateRow 9 30, 235070098479455153144630400⟩, ⟨.privateRow 10 11, 365904052474381621200⟩, ⟨.privateRow 10 12, 1158696166168875133800⟩, ⟨.privateRow 10 13, 5316370644774838849200⟩, ⟨.privateRow 10 14, 23029086302606393284275⟩, ⟨.privateRow 10 15, 82962645497691459580080⟩, ⟨.privateRow 10 16, 209061893981612756284200⟩, ⟨.privateRow 10 17, 450287156268089013535200⟩, ⟨.privateRow 10 18, 862069947629643099547200⟩, ⟨.privateRow 10 19, 1511150472714425697226800⟩, ⟨.privateRow 10 20, 2486098494131938487081280⟩, ⟨.privateRow 10 21, 3909440864653784701441200⟩, ⟨.privateRow 10 22, 7195503191908714580898000⟩, ⟨.privateRow 10 23, 12000450664987301350033200⟩, ⟨.privateRow 10 24, 18746545272446230789750200⟩, ⟨.privateRow 10 25, 18965538847852148190038400⟩, ⟨.privateRow 11 9, 496584071215232200200⟩, ⟨.privateRow 11 10, 1568160224890206948000⟩, ⟨.privateRow 11 11, 6069360870408393558000⟩, ⟨.privateRow 11 12, 23952878729205317892000⟩, ⟨.privateRow 11 13, 77591261127380031281250⟩, ⟨.privateRow 11 14, 185391386587020021408000⟩, ⟨.privateRow 11 15, 379532111571641753010000⟩, ⟨.privateRow 11 16, 699037577172211481820000⟩, ⟨.privateRow 11 17, 1193457051153941387814000⟩, ⟨.privateRow 11 18, 1921328915538207494592000⟩, ⟨.privateRow 11 19, 2959641064442783913192000⟩, ⟨.privateRow 11 21, 19062621033774726085177500⟩, ⟨.privateRow 11 23, 3714448852689936857496000⟩, ⟨.privateRow 12 7, 867051552915484794000⟩, ⟨.privateRow 12 8, 2731212391683777101100⟩, ⟨.privateRow 12 9, 8624881236896138214000⟩, ⟨.privateRow 12 10, 30346804352041967790000⟩, ⟨.privateRow 12 11, 89969349373112657448000⟩, ⟨.privateRow 12 12, 205978934539484856374625⟩, ⟨.privateRow 12 13, 407861050491444047097600⟩, ⟨.privateRow 12 14, 730924459107753681342000⟩, ⟨.privateRow 12 15, 1219941534952087105158000⟩, ⟨.privateRow 12 16, 1928539416572267053054500⟩, ⟨.privateRow 12 17, 2919914338745565337176000⟩, ⟨.privateRow 12 19, 10139878894162289504232000⟩, ⟨.privateRow 12 20, 20597893453948485637462500⟩, ⟨.privateRow 12 21, 6580921286628529586460000⟩, ⟨.privateRow 12 23, 7989706649805609279751200⟩, ⟨.privateRow 13 5, 1986336284860928800800⟩, ⟨.privateRow 13 6, 4161847453994327011200⟩, ⟨.privateRow 13 7, 15294789393429151766160⟩, ⟨.privateRow 13 8, 48299334926618373998400⟩, ⟨.privateRow 13 9, 131098194800821300852800⟩, ⟨.privateRow 13 10, 295613576511655874472000⟩, ⟨.privateRow 13 11, 573554602253593191231000⟩, ⟨.privateRow 13 12, 1010912746575222031020480⟩, ⟨.privateRow 13 13, 1660577134143736477468800⟩, ⟨.privateRow 13 14, 2588348974272625683504000⟩, ⟨.privateRow 13 15, 3871038363146473411292400⟩, ⟨.privateRow 13 18, 37751424613940207930760000⟩, ⟨.privateRow 13 19, 24127530268134486911117400⟩, ⟨.privateRow 13 22, 47964459537793819938677760⟩, ⟨.privateRow 14 3, 6174914972502452576400⟩, ⟨.privateRow 14 4, 12911185851596037205200⟩, ⟨.privateRow 14 5, 33815010563703906966000⟩, ⟨.privateRow 14 6, 99416131057289486480040⟩, ⟨.privateRow 14 7, 254146500447206206039200⟩, ⟨.privateRow 14 8, 568092177470225637028800⟩, ⟨.privateRow 14 9, 1094412871302934683099600⟩, ⟨.privateRow 14 10, 1908434658689039249393625⟩, ⟨.privateRow 14 11, 3105570570170566815757440⟩, ⟨.privateRow 14 12, 4798349998989584398475400⟩, ⟨.privateRow 14 13, 7112077067944555571264400⟩, ⟨.privateRow 14 15, 17262255483583901743352400⟩, ⟨.privateRow 14 19, 210173816657645263356476400⟩, ⟨.privateRow 15 3, 301261003203907534788000⟩, ⟨.privateRow 15 4, 157803382630618232508000⟩, ⟨.privateRow 15 5, 695912917401026405360280⟩, ⟨.privateRow 15 6, 1534845532112539440393600⟩, ⟨.privateRow 15 7, 2982483931718684594401200⟩, ⟨.privateRow 15 8, 5185233502203726157586400⟩, ⟨.privateRow 15 10, 29824839317186845944012000⟩, ⟨.privateRow 15 13, 94003475033059281105015600⟩, ⟨.privateRow 15 17, 83675243639885317787367000⟩, ⟨.privateRow 15 18, 438567161007014191786233600⟩, ⟨.privateRow 15 22, 1328862285132436135949868000⟩, ⟨.privateRow 16 6, 276155919603581906889000⟩, ⟨.privateRow 16 8, 5592157371972533614502250⟩, ⟨.privateRow 16 9, 662774207048596576533600⟩, ⟨.privateRow 16 10, 1065172832756673069429000⟩, ⟨.privateRow 16 11, 764739469671457588308000⟩, ⟨.privateRow 16 15, 2809058014207635156874908000⟩, ⟨.privateRow 16 18, 889774372962740903996358000⟩, ⟨.privateRow 17 7, 69591291740102640536028000⟩, ⟨.privateRow 17 12, 14460528153787561669824000⟩, ⟨.privateRow 17 13, 39766452422915794592016000⟩, ⟨.privateRow 17 14, 25353322666965647707665312000⟩, ⟨.privateRow 17 15, 16930567119056399547550812000⟩, ⟨.hall 16 5, 789443674953423602112000⟩, ⟨.hall 15 6, 27809276162047528648500⟩, ⟨.hall 13 12, 64366760739802893372⟩, ⟨.hall 15 12, 5976020652418871554500⟩, ⟨.hall 16 12, 178174017163228662576000⟩, ⟨.hall 10 18, 5968374647052351600⟩, ⟨.hall 15 19, 156477958962278059606500⟩, ⟨.hall 11 21, 49947512179706248800⟩, ⟨.hall 6 27, 196306424942432322375⟩, ⟨.hall 5 28, 408296321067770635500⟩, ⟨.hall 3 32, 145938593540850893742960⟩, ⟨.hall 2 34, 3127918941116092208685600⟩]
  caps := #[0, 0, 5442681788907420405348000, 1582833702241237057892280, 0, 140196178227141546063840, 129398742411098400347250, 2811584543927354009100, 60028516514585269565460, 0, 5854636466051595366690, 129536119852515575437500, 381521306301935560106775, 200137716332812102223808, 126919897356890237371200, 1558997704016692670710980, 29793134670559986525549750, 0] }

theorem case_56_39_23_checked :
    (Witness.linear .conditional case_56_39_23).check 56 39 23 = true := by
  change case_56_39_23.check 56 39 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_39_24 : Certificate := {
  objectiveScale := 7636328579880000000
  eta := 29354090502018275186409216000
  rows := #[⟨.count 2, 3293629552703390608844136000⟩, ⟨.count 3, 342098967735516146449694400⟩, ⟨.count 4, 31045469806616114542492800⟩, ⟨.count 5, 2232212506068038365872000⟩, ⟨.count 6, 106295833622287541232000⟩, ⟨.path 6, 99316835903579374080000⟩, ⟨.privateRow 2 37, 1488017658906132908449896000⟩, ⟨.privateRow 3 36, 1539606570157483128461160000⟩, ⟨.privateRow 4 29, 240177966922740182450400⟩, ⟨.privateRow 4 30, 5258691102258169748172000⟩, ⟨.privateRow 4 31, 13196627744206998243952800⟩, ⟨.privateRow 5 26, 70863889081525027488000⟩, ⟨.privateRow 5 27, 560710522357566779998800⟩, ⟨.privateRow 5 28, 2654358816739408886764800⟩, ⟨.privateRow 5 29, 5672654320976078450414400⟩, ⟨.privateRow 5 30, 9543948581499790702083840⟩, ⟨.privateRow 5 33, 172330348662906638096692800⟩, ⟨.privateRow 6 23, 13421191113925194600000⟩, ⟨.privateRow 6 24, 60529571923802627646000⟩, ⟨.privateRow 6 25, 321512089351363550640000⟩, ⟨.privateRow 6 26, 1045980529463760041151000⟩, ⟨.privateRow 6 28, 8448550331608483832736000⟩, ⟨.privateRow 6 29, 5539784528948219023874400⟩, ⟨.privateRow 7 19, 115038780976501668000⟩, ⟨.privateRow 7 20, 1734430851645717456000⟩, ⟨.privateRow 7 21, 6979019379241101192000⟩, ⟨.privateRow 7 22, 35431944540762513744000⟩, ⟨.privateRow 7 23, 142855158216619771322400⟩, ⟨.privateRow 7 24, 389751389948387651184000⟩, ⟨.privateRow 7 25, 385725032614210092804000⟩, ⟨.privateRow 7 26, 1227693870581225800896000⟩, ⟨.privateRow 7 27, 4050247054360345226388000⟩, ⟨.privateRow 7 28, 4386152625559664996836800⟩, ⟨.privateRow 7 29, 3115997940920012430282000⟩, ⟨.privateRow 7 30, 4179895760520862606224000⟩, ⟨.privateRow 8 17, 225476010713943269280⟩, ⟨.privateRow 8 18, 966325760202614011200⟩, ⟨.privateRow 8 19, 4682963299443437131200⟩, ⟨.privateRow 8 20, 20010995950862465148600⟩, ⟨.privateRow 8 21, 69180139650868957620000⟩, ⟨.privateRow 8 22, 172714624206880544268480⟩, ⟨.privateRow 8 23, 272074386261491544931200⟩, ⟨.privateRow 8 24, 478431910233648374503500⟩, ⟨.privateRow 8 25, 1087599643108042069605600⟩, ⟨.privateRow 8 26, 3447152410465002681842400⟩, ⟨.privateRow 8 27, 4175364766400801460527040⟩, ⟨.privateRow 8 29, 17135801020908498559831200⟩, ⟨.privateRow 9 14, 58947976657240070400⟩, ⟨.privateRow 9 15, 125264450396635149600⟩, ⟨.privateRow 9 16, 601269361903848718080⟩, ⟨.privateRow 9 17, 2720028065755506105600⟩, ⟨.privateRow 9 18, 10406585109874304736000⟩, ⟨.privateRow 9 20, 137836446145533804614400⟩, ⟨.privateRow 9 21, 90891885207798464549760⟩, ⟨.privateRow 9 22, 177819846474156741254400⟩, ⟨.privateRow 9 23, 271823857360698274632000⟩, ⟨.privateRow 9 24, 761751017783423578310400⟩, ⟨.privateRow 9 25, 2138013639369768733372800⟩, ⟨.privateRow 9 26, 2367598324056721635559680⟩, ⟨.privateRow 9 28, 4371896338109762234572800⟩, ⟨.privateRow 10 13, 132632947478790158400⟩, ⟨.privateRow 10 14, 563690026784858173200⟩, ⟨.privateRow 10 15, 2179601436901451603040⟩, ⟨.privateRow 10 16, 7408497494886707419200⟩, ⟨.privateRow 10 17, 4856406384608008876800⟩, ⟨.privateRow 10 18, 55147674287118624611400⟩, ⟨.privateRow 10 19, 119707263869948062963200⟩, ⟨.privateRow 10 20, 120516927726602677430160⟩, ⟨.privateRow 10 21, 230737117630601945563200⟩, ⟨.privateRow 10 22, 444187741106468240481600⟩, ⟨.privateRow 10 23, 1032196966189758866296800⟩, ⟨.privateRow 10 24, 2420484975014180995720800⟩, ⟨.privateRow 10 25, 3344485666919920513230240⟩, ⟨.privateRow 10 26, 3173293005785359086029400⟩, ⟨.privateRow 10 27, 5275762857355082595703200⟩, ⟨.privateRow 10 29, 22671612877286995726104000⟩, ⟨.privateRow 11 11, 89474607426167964000⟩, ⟨.privateRow 11 12, 568426917766243536000⟩, ⟨.privateRow 11 13, 2013178667088779190000⟩, ⟨.privateRow 11 14, 6227432676861290294400⟩, ⟨.privateRow 11 15, 7132404420543103416000⟩, ⟨.privateRow 11 16, 27503117790382091088000⟩, ⟨.privateRow 11 17, 82942961084057702628000⟩, ⟨.privateRow 11 18, 141142126187169682848000⟩, ⟨.privateRow 11 19, 148653112777835455389600⟩, ⟨.privateRow 11 20, 322108586734204670400000⟩, ⟨.privateRow 11 21, 560468940917516126496000⟩, ⟨.privateRow 11 22, 1193872468974134310504000⟩, ⟨.privateRow 11 24, 8701119253451070761515200⟩, ⟨.privateRow 11 26, 6997272199156039456656000⟩, ⟨.privateRow 12 9, 155403265529660148000⟩, ⟨.privateRow 12 10, 656147121125231736000⟩, ⟨.privateRow 12 11, 2257918034460356268000⟩, ⟨.privateRow 12 12, 6458948223576499901250⟩, ⟨.privateRow 12 13, 10039050953216045560800⟩, ⟨.privateRow 12 14, 20879538747235052742000⟩, ⟨.privateRow 12 15, 60188880149372218860000⟩, ⟨.privateRow 12 16, 135084288561657083649000⟩, ⟨.privateRow 12 18, 685312860659248286665200⟩, ⟨.privateRow 12 19, 285095924128913189292000⟩, ⟨.privateRow 12 20, 833019779463552015835500⟩, ⟨.privateRow 12 21, 1633243919783719681152000⟩, ⟨.privateRow 12 22, 672222725592799913532000⟩, ⟨.privateRow 12 23, 7329688260665738676508800⟩, ⟨.privateRow 13 7, 354319445407625137440⟩, ⟨.privateRow 13 8, 1118903511813553065600⟩, ⟨.privateRow 13 9, 3149506181401112332800⟩, ⟨.privateRow 13 10, 8753774533600150454400⟩, ⟨.privateRow 13 12, 58108389046850522540160⟩, ⟨.privateRow 13 14, 218042735635461623040000⟩, ⟨.privateRow 13 15, 228536042287918213648800⟩, ⟨.privateRow 13 18, 1246417071289490205705600⟩, ⟨.privateRow 13 19, 4373187754943613258853200⟩, ⟨.privateRow 13 21, 3358948342464286302931200⟩, ⟨.privateRow 13 23, 16201256641263659409444000⟩, ⟨.privateRow 14 5, 1096703045309315901600⟩, ⟨.privateRow 14 6, 2303076395149563393360⟩, ⟨.privateRow 14 7, 6060727355656745772000⟩, ⟨.privateRow 14 8, 15353842634330422622400⟩, ⟨.privateRow 14 9, 14902259027438351368800⟩, ⟨.privateRow 14 10, 43182682409054313625500⟩, ⟨.privateRow 14 11, 130507662391808592290400⟩, ⟨.privateRow 14 12, 54286800742811137129200⟩, ⟨.privateRow 14 13, 600571459965924607960800⟩, ⟨.privateRow 14 14, 687084457886286412352400⟩, ⟨.privateRow 14 15, 2093705813772330357600⟩, ⟨.privateRow 14 17, 2784163464358583302195200⟩, ⟨.privateRow 14 19, 20523700789918537782542400⟩, ⟨.privateRow 15 4, 5117947544776807540800⟩, ⟨.privateRow 15 5, 16121534766046943753520⟩, ⟨.privateRow 15 6, 39596752056957405710400⟩, ⟨.privateRow 15 7, 65680326824635696773600⟩, ⟨.privateRow 15 8, 88510386950845965705600⟩, ⟨.privateRow 15 9, 235105715338184596405500⟩, ⟨.privateRow 15 10, 494393732825439608441280⟩, ⟨.privateRow 15 11, 222630718197791128024800⟩, ⟨.privateRow 15 12, 2604247923746044760184000⟩, ⟨.privateRow 15 14, 4377240954660018667622400⟩, ⟨.privateRow 15 16, 7045707786642738381168000⟩, ⟨.privateRow 15 17, 3909472180766383860228600⟩, ⟨.privateRow 15 22, 325475874110081075557176000⟩, ⟨.privateRow 16 2, 73279703482031562516000⟩, ⟨.privateRow 16 7, 47416278723667481628000⟩, ⟨.privateRow 16 19, 414001012792085515590393600⟩, ⟨.privateRow 16 23, 1965215087981122443554088000⟩, ⟨.privateRow 17 3, 1934584171925633250422400⟩, ⟨.privateRow 17 18, 2068715341179143822451686400⟩, ⟨.privateRow 17 22, 17140415763261110598742464000⟩, ⟨.hall 12 10, 388915033628499840⟩, ⟨.hall 13 10, 524635065215220960⟩, ⟨.hall 8 14, 269425121598144512⟩, ⟨.hall 13 14, 18863015299329080880⟩, ⟨.hall 15 15, 1784768656451754723750⟩, ⟨.hall 16 15, 28434642424400276064000⟩, ⟨.hall 6 18, 101754626388760800⟩, ⟨.hall 16 18, 43311442921056902592000⟩, ⟨.hall 7 21, 364319324004168225⟩, ⟨.hall 10 21, 1420621984317513600⟩, ⟨.hall 4 30, 1864584361611883145520⟩, ⟨.hall 3 35, 369783225492100092639766800⟩]
  caps := #[0, 1547890478790628452480000, 0, 83580780169308055233600, 0, 1358710565200441184160, 65969561995643214909000, 0, 667978350434607532320, 0, 3607611703565662888200, 216622733768617176000, 61507579364055019300050, 4349306451943046468160, 147821554366538006277180, 2320557112911901258395000, 10755186180381118043568000, 0] }

theorem case_56_39_24_checked :
    (Witness.linear .conditional case_56_39_24).check 56 39 24 = true := by
  change case_56_39_24.check 56 39 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_39_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 742900, 742900, 534888, 326876, 177650] }

theorem case_56_39_25_checked :
    (Witness.linear .negative case_56_39_25).check 56 39 25 = true := by
  change case_56_39_25.check 56 39 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_40_1_checked :
    (Witness.rising).check 56 40 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_40_2_checked :
    (Witness.rising).check 56 40 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_40_3_checked :
    (Witness.rising).check 56 40 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_40_4_checked :
    (Witness.rising).check 56 40 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_40_5_checked :
    (Witness.rising).check 56 40 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_40_6_checked :
    (Witness.rising).check 56 40 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_40_7_checked :
    (Witness.rising).check 56 40 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_40_8_checked :
    (Witness.rising).check 56 40 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_40_9_checked :
    (Witness.rising).check 56 40 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_40_10_checked :
    (Witness.rising).check 56 40 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_40_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_56_40_11_checked :
    (Witness.linear .positive case_56_40_11).check 56 40 11 = true := by
  change case_56_40_11.check 56 40 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_40_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_56_40_12_checked :
    (Witness.linear .positive case_56_40_12).check 56 40 12 = true := by
  change case_56_40_12.check 56 40 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_40_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_56_40_13_checked :
    (Witness.linear .positive case_56_40_13).check 56 40 13 = true := by
  change case_56_40_13.check 56 40 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_40_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_56_40_14_checked :
    (Witness.linear .positive case_56_40_14).check 56 40 14 = true := by
  change case_56_40_14.check 56 40 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_40_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_56_40_15_checked :
    (Witness.linear .positive case_56_40_15).check 56 40 15 = true := by
  change case_56_40_15.check 56 40 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_40_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_56_40_16_checked :
    (Witness.linear .positive case_56_40_16).check 56 40 16 = true := by
  change case_56_40_16.check 56 40 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_40_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_56_40_17_checked :
    (Witness.linear .positive case_56_40_17).check 56 40 17 = true := by
  change case_56_40_17.check 56 40 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_40_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_56_40_18_checked :
    (Witness.linear .positive case_56_40_18).check 56 40 18 = true := by
  change case_56_40_18.check 56 40 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_40_19 : Certificate := {
  objectiveScale := 5
  eta := 605422560
  rows := #[⟨.assumptionRow 19, 13⟩]
  caps := #[0, 0, 167283600, 46527390, 13037895, 3714500, 1069776, 312018, 92378, 27846, 8580, 2717, 891, 161460, 161460, 67850, 20286] }

theorem case_56_40_19_checked :
    (Witness.linear .conditional case_56_40_19).check 56 40 19 = true := by
  change case_56_40_19.check 56 40 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_40_20 : Certificate := {
  objectiveScale := 22199899072806000000
  eta := 178790546134670702449172155200
  rows := #[⟨.count 2, 14627692509595511526791170560⟩, ⟨.count 3, 1079695751497063971784834320⟩, ⟨.count 4, 65264429936227185197614080⟩, ⟨.count 5, 3588032895799526963989200⟩, ⟨.count 6, 309017187198045384458400⟩, ⟨.count 7, 72104010346210589706960⟩, ⟨.path 4, 12035110941504444812578560⟩, ⟨.path 5, 1885645626623533328954400⟩, ⟨.privateRow 2 37, 1063738447302587128181829720⟩, ⟨.privateRow 2 38, 1687546292812828045031594160⟩, ⟨.privateRow 3 33, 106054698646369175946122880⟩, ⟨.privateRow 3 34, 197134081048690852510964520⟩, ⟨.privateRow 3 35, 408343322720202305533297200⟩, ⟨.privateRow 3 36, 504741806520682929965807040⟩, ⟨.privateRow 3 37, 786572348293904721600411360⟩, ⟨.privateRow 4 29, 5835274551589757009856120⟩, ⟨.privateRow 4 30, 24571280913490294427077920⟩, ⟨.privateRow 4 31, 40865806244790401842487520⟩, ⟨.privateRow 4 32, 89625284860339763005751280⟩, ⟨.privateRow 4 33, 129424123428221358145789380⟩, ⟨.privateRow 4 34, 177022212448551398739130320⟩, ⟨.privateRow 4 35, 256752080269949308433669280⟩, ⟨.privateRow 5 26, 1763801434040399044403112⟩, ⟨.privateRow 5 27, 4754668153147209415438320⟩, ⟨.privateRow 5 28, 9040898678231702810578050⟩, ⟨.privateRow 5 29, 20039028834585628788354720⟩, ⟨.privateRow 5 30, 32600740995343421309649240⟩, ⟨.privateRow 5 31, 47067437839424952658140432⟩, ⟨.privateRow 5 32, 63498740063820575875861500⟩, ⟨.privateRow 5 33, 95806773112401404196343200⟩, ⟨.privateRow 5 34, 85206339083407714007996160⟩, ⟨.privateRow 6 23, 330476714086798536156900⟩, ⟨.privateRow 6 24, 998843433367419424512000⟩, ⟨.privateRow 6 25, 1962259138707588191310840⟩, ⟨.privateRow 6 26, 4787858888068480956732000⟩, ⟨.privateRow 6 27, 8440031925346614563020050⟩, ⟨.privateRow 6 28, 13062107452514204108138400⟩, ⟨.privateRow 6 29, 18758487771022088338048800⟩, ⟨.privateRow 6 30, 24999490444321871602684560⟩, ⟨.privateRow 6 31, 37403955367096743410485500⟩, ⟨.privateRow 6 32, 33442526703432911606942400⟩, ⟨.privateRow 7 20, 46352578079706807668760⟩, ⟨.privateRow 7 21, 214727327514539228687760⟩, ⟨.privateRow 7 22, 472109591552569337367000⟩, ⟨.privateRow 7 23, 1184565884259173973757200⟩, ⟨.privateRow 7 24, 2377372226843629157766624⟩, ⟨.privateRow 7 25, 3926807293616643385469520⟩, ⟨.privateRow 7 26, 5924116992909195057887910⟩, ⟨.privateRow 7 27, 8367008220990885981097440⟩, ⟨.privateRow 7 28, 11066248825992225267882480⟩, ⟨.privateRow 7 29, 16472676192237139294195776⟩, ⟨.privateRow 7 30, 2652397523449889549934600⟩, ⟨.privateRow 8 17, 4506500646638161856685⟩, ⟨.privateRow 8 18, 42728302427384053159680⟩, ⟨.privateRow 8 19, 123034620828851403071400⟩, ⟨.privateRow 8 20, 335869108022946764019600⟩, ⟨.privateRow 8 21, 720372473736678021238980⟩, ⟨.privateRow 8 22, 1332831706399650294583200⟩, ⟨.privateRow 8 23, 2125465993872185494361832⟩, ⟨.privateRow 8 24, 3130738325773119061720720⟩, ⟨.privateRow 8 25, 4349273846299897098573990⟩, ⟨.privateRow 8 26, 5703083865955037595393360⟩, ⟨.privateRow 8 27, 762433146438634198568040⟩, ⟨.privateRow 9 15, 7069020622177508794800⟩, ⟨.privateRow 9 16, 31044782232396226123830⟩, ⟨.privateRow 9 17, 108423067409487034892688⟩, ⟨.privateRow 9 18, 258086576715404571093960⟩, ⟨.privateRow 9 19, 512123355535905983303280⟩, ⟨.privateRow 9 20, 893288572622497861369560⟩, ⟨.privateRow 9 21, 1388912603335591864355280⟩, ⟨.privateRow 9 22, 2006093798965681295846976⟩, ⟨.privateRow 9 23, 1217756619180445515050880⟩, ⟨.privateRow 10 12, 1084270832273843454240⟩, ⟨.privateRow 10 13, 6867048604401008543520⟩, ⟨.privateRow 10 14, 35143131093111043722720⟩, ⟨.privateRow 10 15, 108799801325978479111395⟩, ⟨.privateRow 10 16, 238973291433155097314496⟩, ⟨.privateRow 10 17, 445867655814322626147120⟩, ⟨.privateRow 10 18, 745603008085540273782960⟩, ⟨.privateRow 10 19, 581123988147435347995380⟩, ⟨.privateRow 11 10, 858381075550126067940⟩, ⟨.privateRow 11 11, 9939149295843564997200⟩, ⟨.privateRow 11 12, 46734080779951308143400⟩, ⟨.privateRow 11 13, 132291671643607664588400⟩, ⟨.privateRow 11 14, 275754920520477999325725⟩, ⟨.privateRow 11 15, 246069241657702806142800⟩, ⟨.privateRow 12 8, 1798512729724073666160⟩, ⟨.privateRow 12 9, 18884383662102773494680⟩, ⟨.privateRow 12 10, 75537534648411093978720⟩, ⟨.privateRow 12 11, 130092420783374661852240⟩, ⟨.privateRow 13 6, 5150286453300756407640⟩, ⟨.privateRow 13 7, 43164305513377767987840⟩, ⟨.privateRow 13 8, 22661260394523328193616⟩, ⟨.privateRow 14 4, 21347564139768352646160⟩, ⟨.hall 4 35, 13118351850607393320971040⟩, ⟨.hall 3 36, 86945743935311666766641280⟩, ⟨.assumptionRow 20, 21858649624225183770⟩]
  caps := #[0, 37110654418837590830879640, 1460219957080008878573820, 177279341347059426755280, 261195840951380650041012, 220028400336992967720, 113264807360739398221650, 0, 4258019118807413169210, 220795676440717541657172, 21858649624225183770, 6468941581263633915300, 348773905839255932997390, 12539827886297493862080, 0, 1867283351267124380990400, 519660278575324637210460] }

theorem case_56_40_20_checked :
    (Witness.linear .conditional case_56_40_20).check 56 40 20 = true := by
  change case_56_40_20.check 56 40 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_40_21 : Certificate := {
  objectiveScale := 14799932715204000000
  eta := 131257419394138295396652914400
  rows := #[⟨.count 2, 10001547275122870898252421600⟩, ⟨.count 3, 655476956911587268000342800⟩, ⟨.count 4, 31725764552332659471062400⟩, ⟨.count 5, 1227484938036680277154200⟩, ⟨.count 6, 103005729066015128152800⟩, ⟨.path 4, 15137049198799312776351360⟩, ⟨.path 5, 583925420550086723908800⟩, ⟨.privateRow 2 37, 769019313679980193637106300⟩, ⟨.privateRow 2 38, 1263082001239744005191671800⟩, ⟨.privateRow 3 33, 68788255927575562731721368⟩, ⟨.privateRow 3 34, 134593723455721992389958030⟩, ⟨.privateRow 3 35, 293778061836778812998905200⟩, ⟨.privateRow 3 36, 381747815729407566194956200⟩, ⟨.privateRow 3 37, 620370887683738212073732680⟩, ⟨.privateRow 4 29, 3392107415305210688981895⟩, ⟨.privateRow 4 30, 15029271625939221591266040⟩, ⟨.privateRow 4 31, 26060449453701827422658400⟩, ⟨.privateRow 4 32, 60913467940478706184439808⟩, ⟨.privateRow 4 33, 93449372551915574638423980⟩, ⟨.privateRow 4 34, 134891152498400111072499240⟩, ⟨.privateRow 4 35, 206699021373545907286019940⟩, ⟨.privateRow 5 26, 947996059837559229432936⟩, ⟨.privateRow 5 27, 2700466863680696609739240⟩, ⟨.privateRow 5 28, 5353722768206136285741780⟩, ⟨.privateRow 5 29, 12663328129987202683432560⟩, ⟨.privateRow 5 30, 22110465871045330633354500⟩, ⟨.privateRow 5 31, 33920129933869001751144216⟩, ⟨.privateRow 5 32, 48764199711464886856637430⟩, ⟨.privateRow 5 33, 78615689185333846058352840⟩, ⟨.privateRow 5 34, 78058599867301814240259780⟩, ⟨.privateRow 6 23, 167384309732274583248300⟩, ⟨.privateRow 6 24, 522832109653258605018000⟩, ⟨.privateRow 6 25, 1067826057984356828517360⟩, ⟨.privateRow 6 26, 2785923468535464716058600⟩, ⟨.privateRow 6 27, 5291919330766527208850100⟩, ⟨.privateRow 6 28, 8768975816084216445484200⟩, ⟨.privateRow 6 29, 13440817007989057347160500⟩, ⟨.privateRow 6 30, 19177949989940916609915480⟩, ⟨.privateRow 6 31, 30966097300470797900935500⟩, ⟨.privateRow 6 32, 34212208401176191314528600⟩, ⟨.privateRow 6 33, 11450803547838681746319600⟩, ⟨.privateRow 7 20, 24279921851274994493160⟩, ⟨.privateRow 7 21, 105382784352153938802480⟩, ⟨.privateRow 7 22, 236483986314059731717470⟩, ⟨.privateRow 7 23, 628803155162083259587320⟩, ⟨.privateRow 7 24, 1363795852834040296743072⟩, ⟨.privateRow 7 25, 2423495903303189265150600⟩, ⟨.privateRow 7 26, 3911642561281924491602580⟩, ⟨.privateRow 7 27, 5911057337974039568425680⟩, ⟨.privateRow 7 28, 8388958251351382061977620⟩, ⟨.privateRow 7 29, 13539073028437028444404032⟩, ⟨.privateRow 7 30, 12497170078934285423138460⟩, ⟨.privateRow 8 17, 3505056058496348110755⟩, ⟨.privateRow 8 18, 21097099323520876247592⟩, ⟨.privateRow 8 19, 58369913137408572619920⟩, ⟨.privateRow 8 20, 164236912455257454332520⟩, ⟨.privateRow 8 21, 376543165141321968469680⟩, ⟨.privateRow 8 22, 751265521940567911946760⟩, ⟨.privateRow 8 23, 1282650228492035045787144⟩, ⟨.privateRow 8 24, 2019357376177515095681960⟩, ⟨.privateRow 8 25, 2997824374602519448441455⟩, ⟨.privateRow 8 26, 4213506572850385492161480⟩, ⟨.privateRow 8 27, 6465993890768977419554700⟩, ⟨.privateRow 9 14, 667629725427875830620⟩, ⟨.privateRow 9 15, 4477046394045755570040⟩, ⟨.privateRow 9 16, 15021668822127206188950⟩, ⟨.privateRow 9 17, 50739859132518563127120⟩, ⟨.privateRow 9 18, 124751382979951655207280⟩, ⟨.privateRow 9 19, 263456960880384847006200⟩, ⟨.privateRow 9 20, 492710737365772362997560⟩, ⟨.privateRow 9 21, 816814622255304811680360⟩, ⟨.privateRow 9 22, 995035342777706137956048⟩, ⟨.privateRow 9 23, 2347386114604411420459920⟩, ⟨.privateRow 9 24, 1594299784321767483520560⟩, ⟨.privateRow 10 11, 257514322665037820382⟩, ⟨.privateRow 10 12, 1084270832273843454240⟩, ⟨.privateRow 10 13, 4291905377750630339700⟩, ⟨.privateRow 10 14, 16965649493226021107520⟩, ⟨.privateRow 10 15, 50215292919682374974490⟩, ⟨.privateRow 10 16, 114336359263276792249608⟩, ⟨.privateRow 10 17, 226244726341426085049900⟩, ⟨.privateRow 10 18, 401722343357458999795920⟩, ⟨.privateRow 10 19, 648936093115895307362640⟩, ⟨.privateRow 10 20, 903172960765196282757960⟩, ⟨.privateRow 11 9, 408752893119107651400⟩, ⟨.privateRow 11 10, 1287571613325189101910⟩, ⟨.privateRow 11 11, 6324913188264086816400⟩, ⟨.privateRow 11 12, 22413283639364402885100⟩, ⟨.privateRow 11 13, 61601465421832576640400⟩, ⟨.privateRow 11 14, 130903114021394225360850⟩, ⟨.privateRow 11 15, 246069241657702806142800⟩, ⟨.privateRow 11 16, 354388758334266333763800⟩, ⟨.privateRow 12 7, 858381075550126067940⟩, ⟨.privateRow 12 8, 2697769094586110499240⟩, ⟨.privateRow 12 9, 11330630197261664096808⟩, ⟨.privateRow 12 10, 25841788169193268992720⟩, ⟨.privateRow 12 11, 118551964100978522494380⟩, ⟨.privateRow 12 12, 121082224657011900642360⟩, ⟨.privateRow 13 5, 2463180477665579151480⟩, ⟨.privateRow 13 6, 5150286453300756407640⟩, ⟨.privateRow 13 7, 29675460040447215491640⟩, ⟨.privateRow 13 8, 53820493436992904459838⟩, ⟨.privateRow 14 3, 10229041150305668976285⟩, ⟨.privateRow 14 4, 21347564139768352646160⟩, ⟨.hall 4 35, 17386222558242620130768720⟩, ⟨.hall 3 36, 77052878840107935451847160⟩, ⟨.assumptionRow 21, 11264006790551036340⟩]
  caps := #[0, 0, 747356395995184778580960, 817231210407247151391876, 164219002007115924003564, 0, 61634981701838777980800, 29116970880556216709520, 1536521070628594394253, 12543231272752914906144, 0, 73896508973236422099900, 2518163272154956484448, 502154260150544275836276, 0, 3096860650511322424930200, 1003881395139380831553480] }

theorem case_56_40_21_checked :
    (Witness.linear .conditional case_56_40_21).check 56 40 21 = true := by
  change case_56_40_21.check 56 40 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_40_22 : Certificate := {
  objectiveScale := 278082946280412000000
  eta := 3092488728341471189853976854000
  rows := #[⟨.count 2, 237871851172252197549158109600⟩, ⟨.count 3, 15657797869595893615378975200⟩, ⟨.count 4, 761418349255983827305497600⟩, ⟨.count 5, 17940164478997634819946000⟩, ⟨.path 4, 325099509236487878077785600⟩, ⟨.path 5, 18010741865293067947056000⟩, ⟨.privateRow 2 37, 18654088603343430171912377400⟩, ⟨.privateRow 2 38, 31156022697247018794727904400⟩, ⟨.privateRow 3 33, 1614388190505841900513203840⟩, ⟨.privateRow 3 34, 3190847096426350380462342900⟩, ⟨.privateRow 3 35, 7097317911728085362505584400⟩, ⟨.privateRow 3 36, 9419719414493484446881330800⟩, ⟨.privateRow 3 37, 15623428291330866567618657600⟩, ⟨.privateRow 4 29, 91211573087956395979304400⟩, ⟨.privateRow 4 30, 349549941585522337386526800⟩, ⟨.privateRow 4 31, 604111433350667724094813200⟩, ⟨.privateRow 4 32, 1432871494745710041682339680⟩, ⟨.privateRow 4 33, 2244172943445138345174034500⟩, ⟨.privateRow 4 34, 3317797365594836275280329200⟩, ⟨.privateRow 4 35, 5227669507261600272664791000⟩, ⟨.privateRow 5 25, 3073004250469451323225200⟩, ⟨.privateRow 5 26, 25569455478487155311796720⟩, ⟨.privateRow 5 27, 63934130020474612042544400⟩, ⟨.privateRow 5 28, 122630466405779885381078250⟩, ⟨.privateRow 5 29, 290118088431790323088269600⟩, ⟨.privateRow 5 30, 514599454792300577730030000⟩, ⟨.privateRow 5 31, 806854176347003100333697680⟩, ⟨.privateRow 5 32, 1193398625526584770996302600⟩, ⟨.privateRow 5 33, 1992554268134003974002002400⟩, ⟨.privateRow 5 34, 2087668613845461609836874000⟩, ⟨.privateRow 6 21, 6131293396786614771000⟩, ⟨.privateRow 6 22, 1036660222010536866666000⟩, ⟨.privateRow 6 23, 5772612733074597806896500⟩, ⟨.privateRow 6 24, 13187854706179209589260000⟩, ⟨.privateRow 6 25, 24961721676997666055695200⟩, ⟨.privateRow 6 26, 62976558242860915851198000⟩, ⟨.privateRow 6 27, 119679781458576327022534500⟩, ⟨.privateRow 6 28, 201437513258027441686434000⟩, ⟨.privateRow 6 29, 316027299315038080679910000⟩, ⟨.privateRow 6 30, 465139537219102313695327200⟩, ⟨.privateRow 6 31, 781877862191721082134847500⟩, ⟨.privateRow 6 32, 918410525433598217624604000⟩, ⟨.privateRow 6 33, 495543394915087779021762000⟩, ⟨.privateRow 7 19, 302150138593644375914880⟩, ⟨.privateRow 7 20, 1397934894467348167788000⟩, ⟨.privateRow 7 21, 3244680465579476536813200⟩, ⟨.privateRow 7 22, 5982916096584378693541800⟩, ⟨.privateRow 7 23, 14561264427059411297964000⟩, ⟨.privateRow 7 24, 30469094657727274907598240⟩, ⟨.privateRow 7 25, 54140955705198284858535600⟩, ⟨.privateRow 7 26, 88610678429039513993446200⟩, ⟨.privateRow 7 27, 137078552730637703758201200⟩, ⟨.privateRow 7 28, 200783917381929988551845400⟩, ⟨.privateRow 7 29, 338147207377914462700011840⟩, ⟨.privateRow 7 30, 425851435391173043565713400⟩, ⟨.privateRow 7 31, 32841659950547823359384400⟩, ⟨.privateRow 8 16, 98966288710485123127200⟩, ⟨.privateRow 8 17, 408088669667789101466475⟩, ⟨.privateRow 8 18, 985421474731544725995120⟩, ⟨.privateRow 8 19, 1842658042180937292511200⟩, ⟨.privateRow 8 20, 4166009486669945183068800⟩, ⟨.privateRow 8 21, 8659157538799549523141400⟩, ⟨.privateRow 8 22, 16682246030100540982201200⟩, ⟨.privateRow 8 23, 28372928071233867049688760⟩, ⟨.privateRow 8 24, 45140671168596777827653600⟩, ⟨.privateRow 8 25, 68443730376552260465585850⟩, ⟨.privateRow 8 26, 99108678983017555804352400⟩, ⟨.privateRow 8 27, 166440090549169444573566000⟩, ⟨.privateRow 8 28, 82871542557911371103199360⟩, ⟨.privateRow 9 13, 37949479129584520898400⟩, ⟨.privateRow 9 14, 151329404430318521607200⟩, ⟨.privateRow 9 15, 377014433182800469056000⟩, ⟨.privateRow 9 16, 736061772284233103258550⟩, ⟨.privateRow 9 17, 1618334454437171013422880⟩, ⟨.privateRow 9 18, 3167426168779965190698600⟩, ⟨.privateRow 9 19, 6085701727938714302190000⟩, ⟨.privateRow 9 20, 10945789348390024243014900⟩, ⟨.privateRow 9 21, 17967736719606214626976800⟩, ⟨.privateRow 9 22, 27756038204938509782195880⟩, ⟨.privateRow 9 23, 41099285897340036132967200⟩, ⟨.privateRow 9 24, 58564479514533267861986400⟩, ⟨.privateRow 9 25, 27737153821276407008701200⟩, ⟨.privateRow 10 10, 14715104152287875450400⟩, ⟨.privateRow 10 11, 69528867119560211503140⟩, ⟨.privateRow 10 12, 184326041486553387220800⟩, ⟨.privateRow 10 13, 377687673242055469893600⟩, ⟨.privateRow 10 14, 842223314128006047837600⟩, ⟨.privateRow 10 15, 1619121303756425295651825⟩, ⟨.privateRow 10 16, 2956264424194634177985360⟩, ⟨.privateRow 10 17, 5293758718785563193281400⟩, ⟨.privateRow 10 18, 8993192499225166957956000⟩, ⟨.privateRow 10 19, 14283461097154097770521600⟩, ⟨.privateRow 10 20, 21486058667451973776963600⟩, ⟨.privateRow 10 21, 15013085011371704928270600⟩, ⟨.privateRow 11 7, 7464183265653270156000⟩, ⟨.privateRow 11 8, 39017321615914821270000⟩, ⟨.privateRow 11 9, 110363281142159065878000⟩, ⟨.privateRow 11 10, 244638606531785929362900⟩, ⟨.privateRow 11 11, 564724391809293465750000⟩, ⟨.privateRow 11 12, 1120664181968220144255000⟩, ⟨.privateRow 11 13, 2029818778653827525364000⟩, ⟨.privateRow 11 14, 3497902882866763726855500⟩, ⟨.privateRow 11 15, 5899939259281199840307600⟩, ⟨.privateRow 11 16, 9558686405590332427989000⟩, ⟨.privateRow 11 17, 2159158551576086340126000⟩, ⟨.privateRow 12 4, 7553753464841109397872⟩, ⟨.privateRow 12 5, 23605479577628466868350⟩, ⟨.privateRow 12 6, 82106015922185971716000⟩, ⟨.privateRow 12 7, 197427647376528995626200⟩, ⟨.privateRow 12 8, 485598437025499889863200⟩, ⟨.privateRow 12 9, 358803289579952696398920⟩, ⟨.privateRow 12 10, 3230223521149158624090000⟩, ⟨.privateRow 12 11, 2633322388437664526202600⟩, ⟨.privateRow 12 12, 1777353756433202211264000⟩, ⟨.privateRow 13 2, 21789673456272430955400⟩, ⟨.privateRow 13 3, 90645041578093312774464⟩, ⟨.privateRow 13 4, 212449316198656201815150⟩, ⟨.privateRow 13 5, 541899705086427413325600⟩, ⟨.privateRow 13 6, 1210317316525677755795400⟩, ⟨.privateRow 13 7, 917241492159277569741600⟩, ⟨.privateRow 14 1, 566531509863083204840400⟩, ⟨.privateRow 14 2, 392795180171737688689344⟩, ⟨.privateRow 15 0, 660953428173597072313800⟩, ⟨.hall 4 35, 527189043900369093393150000⟩, ⟨.hall 3 36, 2037890399289653947703464800⟩, ⟨.assumptionRow 22, 116658989634324009600⟩]
  caps := #[0, 0, 0, 6064079196790000044739080, 0, 1176141755506076824007400, 865105489403711387869500, 22660611947628499117845, 29936354663574583593005, 830404662390371789973280, 8035144816753241080920, 69049961130589344744000, 97005920128292713294548, 2779101400588945119094968, 32071937835934690490068272, 0, 48073408128473214603916800] }

theorem case_56_40_22_checked :
    (Witness.linear .conditional case_56_40_22).check 56 40 22 = true := by
  change case_56_40_22.check 56 40 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_40_23 : Certificate := {
  objectiveScale := 782659211668048000000
  eta := 10274528149567072789857104646000
  rows := #[⟨.count 2, 933192142135223685729785971200⟩, ⟨.count 3, 74365388998191510670325674800⟩, ⟨.count 4, 4764068217182503890114854400⟩, ⟨.count 5, 193456159949148286498308000⟩, ⟨.path 5, 194086217821406368181724000⟩, ⟨.path 6, 12962966871812165208000⟩, ⟨.privateRow 2 37, 82626387584889597173991466200⟩, ⟨.privateRow 2 38, 149485257020184699657994750800⟩, ⟨.privateRow 3 33, 4881151249638684070465134720⟩, ⟨.privateRow 3 34, 13274457027467209815288247200⟩, ⟨.privateRow 3 35, 31371019120101668006640841200⟩, ⟨.privateRow 3 36, 44907903634108592019265923600⟩, ⟨.privateRow 4 29, 169694696824959420874059300⟩, ⟨.privateRow 4 30, 1237518628146756647606257200⟩, ⟨.privateRow 4 31, 2278997675574857748987676200⟩, ⟨.privateRow 4 32, 5948524584314637007710147120⟩, ⟨.privateRow 4 33, 9866894992710744616695767700⟩, ⟨.privateRow 4 34, 15543781895044610149951008000⟩, ⟨.privateRow 4 35, 27023722760548742272873428600⟩, ⟨.privateRow 5 25, 3593849611703545243249200⟩, ⟨.privateRow 5 26, 67457321860529098161583920⟩, ⟨.privateRow 5 28, 889162361244536445063147150⟩, ⟨.privateRow 5 30, 3910197586566371851664713800⟩, ⟨.privateRow 5 31, 2592480766066368907152543120⟩, ⟨.privateRow 5 32, 5488056867948718618825370100⟩, ⟨.privateRow 5 33, 10035608390173643140464400800⟩, ⟨.privateRow 5 34, 12540164733399355666970756400⟩, ⟨.privateRow 6 20, 50976590236929719762400⟩, ⟨.privateRow 6 21, 273088876269266355870000⟩, ⟨.privateRow 6 22, 352914855486436521432000⟩, ⟨.privateRow 6 24, 59538340278995870422494000⟩, ⟨.privateRow 6 25, 8372904946415706470974200⟩, ⟨.privateRow 6 26, 391712615478940788274242000⟩, ⟨.privateRow 6 27, 155606041698227969574726000⟩, ⟨.privateRow 6 28, 1038338525351004538288914000⟩, ⟨.privateRow 6 29, 1583269172021240933670441000⟩, ⟨.privateRow 6 30, 1843033131721075553149690800⟩, ⟨.privateRow 6 32, 12837179836414826679166380000⟩, ⟨.privateRow 6 33, 1336032709372131792822801000⟩, ⟨.privateRow 7 17, 26987606596021616344800⟩, ⟨.privateRow 7 18, 114697328033091869465400⟩, ⟨.privateRow 7 19, 183515724852946991144640⟩, ⟨.privateRow 7 21, 7375920479666523297928800⟩, ⟨.privateRow 7 23, 64042817161750023841498800⟩, ⟨.privateRow 7 24, 149702952548791508026240080⟩, ⟨.privateRow 7 25, 97059427811114186427609600⟩, ⟨.privateRow 7 26, 401870763095945637639395250⟩, ⟨.privateRow 7 27, 625231520440959936437247600⟩, ⟨.privateRow 7 28, 973436223016850696152849800⟩, ⟨.privateRow 7 30, 3700938683643775352040061800⟩, ⟨.privateRow 7 31, 3144465480469891298683762800⟩, ⟨.privateRow 7 32, 2193930490616981279134171200⟩, ⟨.privateRow 8 14, 9390424517329158903600⟩, ⟨.privateRow 8 15, 49560573841459449769000⟩, ⟨.privateRow 8 16, 62971082057383771471200⟩, ⟨.privateRow 8 17, 11151129114328376198025⟩, ⟨.privateRow 8 18, 725566801038966344618160⟩, ⟨.privateRow 8 19, 3976174038480518141467200⟩, ⟨.privateRow 8 21, 36248603707643441561046600⟩, ⟨.privateRow 8 22, 76476470944084790943546000⟩, ⟨.privateRow 8 23, 73882921059894089337634440⟩, ⟨.privateRow 8 24, 141743241186574026339340000⟩, ⟨.privateRow 8 25, 290620726977626140472927550⟩, ⟨.privateRow 8 26, 426877966644049473290337600⟩, ⟨.privateRow 8 27, 778170394114291404602976600⟩, ⟨.privateRow 8 29, 1284297842355427743478935300⟩, ⟨.privateRow 8 30, 2180387709810703616917293600⟩, ⟨.privateRow 9 11, 8496098372821619960400⟩, ⟨.privateRow 9 12, 26762709874388102875260⟩, ⟨.privateRow 9 13, 37561698069316635614400⟩, ⟨.privateRow 9 14, 9912114768291889953800⟩, ⟨.privateRow 9 15, 41980721371589180980800⟩, ⟨.privateRow 9 16, 33453387342985128594075⟩, ⟨.privateRow 9 20, 103958259689845341835454400⟩, ⟨.privateRow 9 21, 24102658711115588407658400⟩, ⟨.privateRow 9 22, 74400333450798925993222800⟩, ⟨.privateRow 9 23, 131692356811526049926186800⟩, ⟨.privateRow 9 24, 233170109780606346300702750⟩, ⟨.privateRow 9 25, 399987815294069046115671600⟩, ⟨.privateRow 9 26, 617504925835048160341832400⟩, ⟨.privateRow 9 27, 112938635669917794133597200⟩, ⟨.privateRow 9 28, 560188122187400306683983900⟩, ⟨.privateRow 10 8, 9973680698529727779600⟩, ⟨.privateRow 10 9, 20854059642380339902800⟩, ⟨.privateRow 10 10, 32770665152311962704400⟩, ⟨.privateRow 10 11, 34409198409927560839620⟩, ⟨.privateRow 10 12, 24146805901703551466400⟩, ⟨.privateRow 10 13, 50976590236929719762400⟩, ⟨.privateRow 10 14, 80962819788064849034400⟩, ⟨.privateRow 10 15, 100360162028955385782225⟩, ⟨.privateRow 10 16, 244687633137262654859520⟩, ⟨.privateRow 10 17, 606257305317771310031400⟩, ⟨.privateRow 10 18, 60824875343087334468805200⟩, ⟨.privateRow 10 19, 72813687079674488465618100⟩, ⟨.privateRow 10 20, 44773666052190589771311600⟩, ⟨.privateRow 10 22, 342843057638470830262021200⟩, ⟨.privateRow 10 23, 208146976048053470112334650⟩, ⟨.privateRow 10 27, 2169672005737982348742239100⟩, ⟨.privateRow 11 6, 31860368898081074851500⟩, ⟨.privateRow 11 7, 16622801164216212966000⟩, ⟨.privateRow 11 8, 34756766070633899838000⟩, ⟨.privateRow 11 9, 36411850169235514116000⟩, ⟨.privateRow 11 10, 19116221338848644910900⟩, ⟨.privateRow 11 11, 80489353005678504888000⟩, ⟨.privateRow 11 12, 106201229660270249505000⟩, ⟨.privateRow 11 13, 134938032980108081724000⟩, ⟨.privateRow 11 14, 286743320082729673663500⟩, ⟨.privateRow 11 15, 662695673080086356911200⟩, ⟨.privateRow 11 17, 169575588061232748548076000⟩, ⟨.privateRow 11 18, 47471949658140801528735000⟩, ⟨.privateRow 11 19, 53942500941623812548576000⟩, ⟨.privateRow 11 20, 3287990070281966924674800⟩, ⟨.privateRow 11 21, 519748817957362601077470000⟩, ⟨.privateRow 11 22, 285214022375621782070628000⟩, ⟨.privateRow 11 28, 3963175007970101062927788000⟩, ⟨.privateRow 12 3, 32350528419590014464600⟩, ⟨.privateRow 12 5, 105139217363667547009950⟩, ⟨.privateRow 12 7, 38232442677697289821800⟩, ⟨.privateRow 12 9, 42055686945467018803980⟩, ⟨.privateRow 12 12, 395818230074983706390400⟩, ⟨.privateRow 12 15, 50106347017884990975027600⟩, ⟨.privateRow 12 17, 148106110859619684554682900⟩, ⟨.privateRow 12 19, 1229287729416000959640335400⟩, ⟨.privateRow 13 2, 97051585258770043393800⟩, ⟨.privateRow 13 3, 201867297338241690259104⟩, ⟨.privateRow 13 5, 109710487683827005575600⟩, ⟨.privateRow 13 7, 360477316675431589748400⟩, ⟨.privateRow 13 8, 126167060836401056411940⟩, ⟨.privateRow 13 9, 265614864918739066130400⟩, ⟨.privateRow 13 11, 2820204889284258908031600⟩, ⟨.privateRow 13 13, 1177559234473076526511440⟩, ⟨.privateRow 13 14, 179517703704364931694703200⟩, ⟨.privateRow 13 15, 4852579262938502169690000⟩, ⟨.privateRow 13 16, 381024523725931190364058800⟩, ⟨.privateRow 13 17, 18580967141360882853394800⟩, ⟨.privateRow 13 18, 34569774669173889456871560⟩, ⟨.privateRow 13 19, 1005972031735571089791201600⟩, ⟨.privateRow 13 27, 38776184477459500677645639600⟩, ⟨.privateRow 14 4, 4278709019669253217448400⟩, ⟨.privateRow 14 5, 994043509620129535366800⟩, ⟨.privateRow 14 9, 4859768269253966617348800⟩, ⟨.privateRow 14 10, 6432046238718485228844000⟩, ⟨.privateRow 14 12, 119550299423647578786780480⟩, ⟨.privateRow 14 13, 592023913086617147563455600⟩, ⟨.privateRow 14 15, 1488000296942198903649485700⟩, ⟨.privateRow 15 2, 22324560486885409148446050⟩, ⟨.privateRow 15 5, 25513783413583324741081200⟩, ⟨.privateRow 15 8, 29766080649180545531261400⟩, ⟨.privateRow 15 10, 62189847070609354056385425⟩, ⟨.privateRow 15 14, 12074398000478308433716677900⟩, ⟨.privateRow 16 3, 417498274040454404854056000⟩, ⟨.privateRow 16 7, 510275668271666494821624000⟩, ⟨.privateRow 16 9, 717575158507031008342908750⟩, ⟨.privateRow 16 13, 144950182018420263685267567500⟩, ⟨.privateRow 16 14, 24110525325836241880321734000⟩, ⟨.hall 15 1, 229624050722249922669730800⟩, ⟨.hall 12 2, 20026517593079532763800⟩, ⟨.hall 11 4, 2585209167630072310800⟩, ⟨.hall 8 8, 2069441262482434456⟩, ⟨.hall 14 8, 171624297830629792900752⟩, ⟨.hall 15 8, 2575262681978495769580320⟩, ⟨.hall 11 9, 495681558525724839840⟩, ⟨.hall 13 9, 10664256017071201328784⟩, ⟨.hall 14 9, 48993519220847785584⟩, ⟨.hall 8 11, 30494020883995886910⟩, ⟨.hall 7 12, 7297284617656585440⟩, ⟨.hall 11 21, 1836983650024907519520⟩, ⟨.hall 5 31, 307024185158609013327375⟩, ⟨.hall 4 35, 5035187212357614604671178800⟩, ⟨.hall 3 36, 10675301910218576520719029200⟩]
  caps := #[0, 709308072302517463843782000, 65534914232942313529347120, 7349421681787718343885360, 19491768529220426192942760, 862608616739032609160000, 518845787317467113949000, 1712455529385851384259420, 604146131378541876921325, 3892085629094956341943830, 0, 1006748743290421443716850, 462398522537246866876052, 35690965859646398435039928, 15835901283733321390342028, 6378445853395831185270300, 0] }

theorem case_56_40_23_checked :
    (Witness.linear .conditional case_56_40_23).check 56 40 23 = true := by
  change case_56_40_23.check 56 40 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_40_24 : Certificate := {
  objectiveScale := 116285185619460000000
  eta := 1517245032509619023379220452000
  rows := #[⟨.count 2, 125414591089083697277398922400⟩, ⟨.count 3, 8749512638325457015555137600⟩, ⟨.count 4, 466821964127180560788489600⟩, ⟨.count 5, 14163287746577080121010000⟩, ⟨.path 4, 110809833983365184290022400⟩, ⟨.path 5, 14415393206010874581504000⟩, ⟨.privateRow 2 38, 52035541493250950309120846400⟩, ⟨.privateRow 3 33, 534692439008777928728369520⟩, ⟨.privateRow 3 34, 1769419538179874619517779300⟩, ⟨.privateRow 3 36, 13950366320786871349857483000⟩, ⟨.privateRow 4 29, 10480832932467039289547400⟩, ⟨.privateRow 4 30, 129573849612970887278497200⟩, ⟨.privateRow 4 31, 259943541108844677154270200⟩, ⟨.privateRow 4 32, 776034862210451373990379920⟩, ⟨.privateRow 5 26, 4702211531863590600175320⟩, ⟨.privateRow 5 27, 20437099652097890426464800⟩, ⟨.privateRow 5 28, 45511364625667684122178800⟩, ⟨.privateRow 5 29, 125203463679741388269728400⟩, ⟨.privateRow 5 30, 270424374041311716443817600⟩, ⟨.privateRow 5 31, 372362277049342487768100240⟩, ⟨.privateRow 5 32, 619879893708523539962871000⟩, ⟨.privateRow 5 33, 1112038405915691988523389600⟩, ⟨.privateRow 5 34, 1520759416309136349526580400⟩, ⟨.privateRow 6 21, 12262586793573229542000⟩, ⟨.privateRow 6 22, 46220519452699095966000⟩, ⟨.privateRow 6 23, 1051516817548904433226500⟩, ⟨.privateRow 6 24, 3417917373554138343252000⟩, ⟨.privateRow 6 25, 7794100165995144696895200⟩, ⟨.privateRow 6 26, 22813861474621128383472000⟩, ⟨.privateRow 6 27, 50215292919682374974490000⟩, ⟨.privateRow 6 29, 359704589709280328770257000⟩, ⟨.privateRow 6 30, 157324083526827105732043200⟩, ⟨.privateRow 6 32, 1600022324825434990640160000⟩, ⟨.privateRow 7 18, 3218929033312972754775⟩, ⟨.privateRow 7 19, 17167621511002521358800⟩, ⟨.privateRow 7 20, 231762890398534038343800⟩, ⟨.privateRow 7 21, 701231309410949141655600⟩, ⟨.privateRow 7 22, 1536502125234725661612600⟩, ⟨.privateRow 7 23, 4462020899996018960437200⟩, ⟨.privateRow 7 24, 10805300979024986943228720⟩, ⟨.privateRow 7 25, 21882994886024547225350400⟩, ⟨.privateRow 7 26, 21277120910198749909062750⟩, ⟨.privateRow 7 27, 61671001502238486012626400⟩, ⟨.privateRow 7 28, 198586461828521665817919000⟩, ⟨.privateRow 7 29, 187501328618867337776541840⟩, ⟨.privateRow 7 30, 203075794853648825153245200⟩, ⟨.privateRow 8 15, 2225432418092919435400⟩, ⟨.privateRow 8 16, 7069020622177508794800⟩, ⟨.privateRow 8 18, 296427598089976868795280⟩, ⟨.privateRow 8 19, 340491159968216673616200⟩, ⟨.privateRow 8 20, 1059990579448565934153600⟩, ⟨.privateRow 8 21, 2617108523677273256030400⟩, ⟨.privateRow 8 22, 5735546277539478726690000⟩, ⟨.privateRow 8 23, 10935774902508606105555600⟩, ⟨.privateRow 8 24, 15190801685902268066040400⟩, ⟨.privateRow 8 25, 23699186178376022297433450⟩, ⟨.privateRow 8 26, 50100842109609024832098000⟩, ⟨.privateRow 8 27, 163582635324338136018512400⟩, ⟨.privateRow 8 28, 160239145659395333858767440⟩, ⟨.privateRow 8 29, 200989928840062018808151000⟩, ⟨.privateRow 8 30, 164557374723462834731217600⟩, ⟨.privateRow 9 12, 2002889176283627491860⟩, ⟨.privateRow 9 13, 4216608792176057877600⟩, ⟨.privateRow 9 14, 4450864836185838870800⟩, ⟨.privateRow 9 15, 37701443318280046905600⟩, ⟨.privateRow 9 16, 222821420861553558469425⟩, ⟨.privateRow 9 17, 299098116991688372117760⟩, ⟨.privateRow 9 18, 804016940765284750303800⟩, ⟨.privateRow 9 19, 1799518890691751469609600⟩, ⟨.privateRow 9 20, 3631905706327644518572800⟩, ⟨.privateRow 9 21, 6580401348262754323256400⟩, ⟨.privateRow 9 22, 10130613453642587853827880⟩, ⟨.privateRow 9 23, 14500917636293463041066400⟩, ⟨.privateRow 9 24, 22111896506171247510134400⟩, ⟨.privateRow 9 25, 52103731285892652323958000⟩, ⟨.privateRow 9 26, 136536955147254886120096200⟩, ⟨.privateRow 9 27, 139769618277776660891958240⟩, ⟨.privateRow 9 28, 157677450402928574296678500⟩, ⟨.privateRow 10 10, 2452517358714645908400⟩, ⟨.privateRow 10 11, 2575143226650378203820⟩, ⟨.privateRow 10 12, 8132031242053825906800⟩, ⟨.privateRow 10 14, 327194668797930407073600⟩, ⟨.privateRow 10 15, 263952180731663765891550⟩, ⟨.privateRow 10 16, 734774200670907914156640⟩, ⟨.privateRow 10 17, 1523013279761795109116400⟩, ⟨.privateRow 10 18, 2876236896227960886112800⟩, ⟨.privateRow 10 19, 4987194048946232454731400⟩, ⟨.privateRow 10 20, 7851845801986698632374800⟩, ⟨.privateRow 10 21, 11382133061794671660884400⟩, ⟨.privateRow 10 22, 15874327357173664749770400⟩, ⟨.privateRow 10 23, 27959617583356481347975650⟩, ⟨.privateRow 10 24, 56667866090460608359490400⟩, ⟨.privateRow 10 25, 130757189238550703929300200⟩, ⟨.privateRow 10 26, 143950506369756141593538000⟩, ⟨.privateRow 11 8, 3901732161591482127000⟩, ⟨.privateRow 11 9, 4087528931191076514000⟩, ⟨.privateRow 11 10, 12875716133251891019100⟩, ⟨.privateRow 11 12, 438728105281175545836000⟩, ⟨.privateRow 11 13, 363549631997700452304000⟩, ⟨.privateRow 11 14, 820826903494808052467625⟩, ⟨.privateRow 11 15, 1636646584048907036205600⟩, ⟨.privateRow 11 16, 2936889537060788475309000⟩, ⟨.privateRow 11 17, 4912580924686875342672000⟩, ⟨.privateRow 11 18, 7675357450544043924163500⟩, ⟨.privateRow 11 19, 11252595554029834454268000⟩, ⟨.privateRow 11 20, 15639703196523296957866800⟩, ⟨.privateRow 11 21, 24797675515892530851600000⟩, ⟨.privateRow 11 22, 39228015152640761304858000⟩, ⟨.privateRow 11 23, 74372588903021637172230000⟩, ⟨.privateRow 11 24, 155996454129976244080296000⟩, ⟨.privateRow 11 26, 417259040824916281625634000⟩, ⟨.privateRow 12 6, 8210601592218597171600⟩, ⟨.privateRow 12 7, 8583810755501260679400⟩, ⟨.privateRow 12 8, 17985127297240736661600⟩, ⟨.privateRow 12 10, 695740450709049549804000⟩, ⟨.privateRow 12 11, 681936076687044598419000⟩, ⟨.privateRow 12 12, 1199713785592411492603200⟩, ⟨.privateRow 12 13, 2289731519029961286229950⟩, ⟨.privateRow 12 14, 3990899747257719465209040⟩, ⟨.privateRow 12 15, 6474645827006665198176000⟩, ⟨.privateRow 12 17, 34542685115262989850685500⟩, ⟨.privateRow 12 18, 10420746257178530464791600⟩, ⟨.privateRow 12 19, 31574689483035837283104960⟩, ⟨.privateRow 12 20, 45217607546479418756706000⟩, ⟨.privateRow 12 22, 258122546969999052567283200⟩, ⟨.privateRow 12 23, 163129600867797791704877400⟩, ⟨.privateRow 12 25, 548638556343240826954190700⟩, ⟨.privateRow 13 2, 21789673456272430955400⟩, ⟨.privateRow 13 4, 23605479577628466868350⟩, ⟨.privateRow 13 5, 24631804776655791514800⟩, ⟨.privateRow 13 6, 51502864533007564076400⟩, ⟨.privateRow 13 8, 1416328774657708012101000⟩, ⟨.privateRow 13 9, 1699594529589249614521200⟩, ⟨.privateRow 13 10, 2486443848843531843466200⟩, ⟨.privateRow 13 11, 4365625164239052931417200⟩, ⟨.privateRow 13 12, 7435726066952967063530250⟩, ⟨.privateRow 13 13, 11859392939800541754659040⟩, ⟨.privateRow 13 16, 4437830160594151771249800⟩, ⟨.privateRow 13 18, 56653150986308320484040⟩, ⟨.privateRow 13 19, 103423474522782856172530800⟩, ⟨.privateRow 13 21, 1861460675264416244475600⟩, ⟨.privateRow 13 22, 119915836254352611691218000⟩, ⟨.privateRow 14 3, 511452057515283448814250⟩, ⟨.privateRow 14 6, 3740906477826073225612800⟩, ⟨.privateRow 14 8, 19510550067740918089503600⟩, ⟨.privateRow 14 10, 32925478337925070963665600⟩, ⟨.privateRow 14 11, 25316876847006530716305375⟩, ⟨.privateRow 14 13, 53307917309021543464982400⟩, ⟨.privateRow 14 18, 309871753246593065521593600⟩, ⟨.privateRow 14 19, 101881249857044463003798600⟩, ⟨.privateRow 14 21, 232812976580957025900246600⟩, ⟨.privateRow 15 1, 2749566261202163820825408⟩, ⟨.privateRow 15 2, 716032880521396828339950⟩, ⟨.privateRow 15 6, 3436957826502704776031760⟩, ⟨.privateRow 15 9, 297195764997586824750981600⟩, ⟨.privateRow 15 15, 1971563989566551557887309600⟩, ⟨.privateRow 15 18, 1031087347950811432809528000⟩, ⟨.privateRow 15 19, 267591716491996300419615600⟩, ⟨.privateRow 15 20, 727489406609739177593389200⟩, ⟨.privateRow 16 1, 64442959246925714550595500⟩, ⟨.privateRow 16 5, 25777183698770285820238200⟩, ⟨.privateRow 16 13, 25841626658017211534788795500⟩, ⟨.privateRow 16 22, 90048295054370865132032112000⟩, ⟨.hall 13 13, 56789758977482603072⟩, ⟨.hall 8 18, 1678323275117713224⟩, ⟨.hall 9 18, 5700314487720954816⟩, ⟨.hall 11 19, 54682661286837144000⟩, ⟨.hall 14 21, 117822132848336869412460⟩, ⟨.hall 5 23, 6751410536894506560⟩, ⟨.hall 10 26, 9824164362207518380200⟩, ⟨.hall 7 27, 367930304781888651075⟩, ⟨.hall 4 30, 5014785257042866262100⟩, ⟨.hall 2 35, 9399077413159957228906200⟩]
  caps := #[0, 0, 1410894277257011618728800, 0, 458772633728076586449960, 252105459433794460494000, 910498904971591897329450, 119578840237801490081850, 201201732557677820849440, 55248513642134093518720, 67679564256434576704050, 0, 1758480453591380413477110, 0, 437802961233082632184998, 0, 0] }

theorem case_56_40_24_checked :
    (Witness.linear .conditional case_56_40_24).check 56 40 24 = true := by
  change case_56_40_24.check 56 40 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_40_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2674440, 2674440, 1931540, 1188640, 653752] }

theorem case_56_40_25_checked :
    (Witness.linear .negative case_56_40_25).check 56 40 25 = true := by
  change case_56_40_25.check 56 40 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_40_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 742900, 742900, 534888] }

theorem case_56_40_26_checked :
    (Witness.linear .negative case_56_40_26).check 56 40 26 = true := by
  change case_56_40_26.check 56 40 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_41_1_checked :
    (Witness.rising).check 56 41 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_41_2_checked :
    (Witness.rising).check 56 41 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_41_3_checked :
    (Witness.rising).check 56 41 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_41_4_checked :
    (Witness.rising).check 56 41 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_41_5_checked :
    (Witness.rising).check 56 41 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_41_6_checked :
    (Witness.rising).check 56 41 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_41_7_checked :
    (Witness.rising).check 56 41 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_41_8_checked :
    (Witness.rising).check 56 41 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_41_9_checked :
    (Witness.rising).check 56 41 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_41_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_56_41_10_checked :
    (Witness.linear .positive case_56_41_10).check 56 41 10 = true := by
  change case_56_41_10.check 56 41 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_41_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_56_41_11_checked :
    (Witness.linear .positive case_56_41_11).check 56 41 11 = true := by
  change case_56_41_11.check 56 41 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_41_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_56_41_12_checked :
    (Witness.linear .positive case_56_41_12).check 56 41 12 = true := by
  change case_56_41_12.check 56 41 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_41_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_56_41_13_checked :
    (Witness.linear .positive case_56_41_13).check 56 41 13 = true := by
  change case_56_41_13.check 56 41 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_41_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_56_41_14_checked :
    (Witness.linear .positive case_56_41_14).check 56 41 14 = true := by
  change case_56_41_14.check 56 41 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_41_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_56_41_15_checked :
    (Witness.linear .positive case_56_41_15).check 56 41 15 = true := by
  change case_56_41_15.check 56 41 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_41_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_56_41_16_checked :
    (Witness.linear .positive case_56_41_16).check 56 41 16 = true := by
  change case_56_41_16.check 56 41 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_41_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_56_41_17_checked :
    (Witness.linear .positive case_56_41_17).check 56 41 17 = true := by
  change case_56_41_17.check 56 41 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_41_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_56_41_18_checked :
    (Witness.linear .positive case_56_41_18).check 56 41 18 = true := by
  change case_56_41_18.check 56 41 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_41_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_56_41_19_checked :
    (Witness.linear .positive case_56_41_19).check 56 41 19 = true := by
  change case_56_41_19.check 56 41 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_41_20 : Certificate := {
  objectiveScale := 3
  eta := 354817320
  rows := #[⟨.assumptionRow 20, 5⟩]
  caps := #[0, 0, 99249600, 28514250, 8259300, 2414425, 713184, 213180, 64600, 19890, 6240, 4942470, 3511755, 1735695, 699660, 239200] }

theorem case_56_41_20_checked :
    (Witness.linear .conditional case_56_41_20).check 56 41 20 = true := by
  change case_56_41_20.check 56 41 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_41_21 : Certificate := {
  objectiveScale := 148261836153600000
  eta := 2526627807508597681868179200
  rows := #[⟨.count 2, 189597507972028315714114560⟩, ⟨.count 3, 12196356736047546943520640⟩, ⟨.count 4, 604741539210464687391360⟩, ⟨.count 5, 20064417359338576224000⟩, ⟨.count 6, 2407730083120629146880⟩, ⟨.path 4, 251985252558994015501440⟩, ⟨.path 5, 12125212537812136963200⟩, ⟨.privateRow 2 38, 14259982061455519508159040⟩, ⟨.privateRow 2 39, 22064237837543852116246080⟩, ⟨.privateRow 3 33, 133160849874810350873280⟩, ⟨.privateRow 3 34, 1428426000646031918539008⟩, ⟨.privateRow 3 35, 2651813720296982926644960⟩, ⟨.privateRow 3 36, 5557442320189598842523520⟩, ⟨.privateRow 3 37, 6683056134048492968689920⟩, ⟨.privateRow 3 38, 10112867637453829188420480⟩, ⟨.privateRow 4 30, 119320581983816595482100⟩, ⟨.privateRow 4 31, 335792356235216314948800⟩, ⟨.privateRow 4 32, 554898182420307774288240⟩, ⟨.privateRow 4 33, 1239720155381452609152288⟩, ⟨.privateRow 4 34, 1789119015410521668673800⟩, ⟨.privateRow 4 35, 2421908938054561740744960⟩, ⟨.privateRow 4 36, 3446916419204172355961520⟩, ⟨.privateRow 5 26, 1422749594571280859520⟩, ⟨.privateRow 5 27, 32664871461003202092672⟩, ⟨.privateRow 5 28, 70091697975289426275840⟩, ⟨.privateRow 5 29, 125854057886451219365040⟩, ⟨.privateRow 5 30, 281991054258818446988160⟩, ⟨.privateRow 5 31, 464357499086292449077440⟩, ⟨.privateRow 5 32, 670151539801908445881600⟩, ⟨.privateRow 5 33, 901494271955082229744320⟩, ⟨.privateRow 5 34, 1351137864977859722924160⟩, ⟨.privateRow 5 35, 1115180316832038066529920⟩, ⟨.privateRow 6 23, 46302501598473637440⟩, ⟨.privateRow 6 24, 7507436161952517270480⟩, ⟨.privateRow 6 25, 16671706787668598789760⟩, ⟨.privateRow 6 26, 29534822352946384201728⟩, ⟨.privateRow 6 27, 69846466207564177010880⟩, ⟨.privateRow 6 28, 124248904497704133267120⟩, ⟨.privateRow 6 29, 193564300610876293200960⟩, ⟨.privateRow 6 30, 278962282686004004767680⟩, ⟨.privateRow 6 31, 372475843858761329022336⟩, ⟨.privateRow 6 32, 560148371629334701733520⟩, ⟨.privateRow 6 33, 306918704206682420973120⟩, ⟨.privateRow 7 21, 1528717513092462950400⟩, ⟨.privateRow 7 22, 4558224046249738085760⟩, ⟨.privateRow 7 23, 8293292508526611505920⟩, ⟨.privateRow 7 24, 18945674088393637428480⟩, ⟨.privateRow 7 25, 37012161888859893607872⟩, ⟨.privateRow 7 26, 61411979650953331079680⟩, ⟨.privateRow 7 27, 92998574460534300798240⟩, ⟨.privateRow 7 28, 132004757255534175767040⟩, ⟨.privateRow 7 29, 175719708473674064219520⟩, ⟨.privateRow 7 30, 198905257422243085633920⟩, ⟨.privateRow 8 18, 329181847301648516175⟩, ⟨.privateRow 8 19, 1310875267476786979968⟩, ⟨.privateRow 8 20, 2892620169304644738960⟩, ⟨.privateRow 8 21, 6473346959586606034320⟩, ⟨.privateRow 8 22, 12621075863950612738680⟩, ⟨.privateRow 8 23, 22738152975632254676880⟩, ⟨.privateRow 8 24, 36142703803288555304832⟩, ⟨.privateRow 8 25, 53332336030975232190960⟩, ⟨.privateRow 8 26, 74409727794497082367380⟩, ⟨.privateRow 8 27, 55411232607373368005280⟩, ⟨.privateRow 9 15, 89175188263727005440⟩, ⟨.privateRow 9 16, 417025145115664525440⟩, ⟨.privateRow 9 17, 1120263302563070505840⟩, ⟨.privateRow 9 18, 2898193618571127676800⟩, ⟨.privateRow 9 19, 5618036860614801342720⟩, ⟨.privateRow 9 20, 10176260906864539428480⟩, ⟨.privateRow 9 21, 17188517537833380298560⟩, ⟨.privateRow 9 22, 26485030914326920615680⟩, ⟨.privateRow 9 23, 29909358143654037624576⟩, ⟨.privateRow 10 12, 30096626039007864336⟩, ⟨.privateRow 10 13, 147843075279336877440⟩, ⟨.privateRow 10 14, 479316636917532654240⟩, ⟨.privateRow 10 15, 1487127404280388590720⟩, ⟨.privateRow 10 16, 3385870429388384737800⟩, ⟨.privateRow 10 17, 6126335433718045273728⟩, ⟨.privateRow 10 18, 10433497026856059636480⟩, ⟨.privateRow 10 19, 10649575367648936611200⟩, ⟨.privateRow 11 9, 18240379417580523840⟩, ⟨.privateRow 11 10, 76435875654623147520⟩, ⟨.privateRow 11 11, 240773008312062914688⟩, ⟨.privateRow 11 12, 865938012350401710720⟩, ⟨.privateRow 11 13, 2363142488988765644160⟩, ⟨.privateRow 11 14, 5027906938281313806720⟩, ⟨.privateRow 11 15, 2633454778413188129400⟩, ⟨.privateRow 12 7, 47980128467983551840⟩, ⟨.privateRow 12 8, 150483130195039321680⟩, ⟨.privateRow 12 9, 630595974150640967040⟩, ⟨.privateRow 12 10, 1931200170836337961560⟩, ⟨.privateRow 12 11, 1045461746618167919040⟩, ⟨.privateRow 13 6, 767682055487736829440⟩, ⟨.privateRow 13 7, 401288347186771524480⟩, ⟨.hall 4 36, 18730404745717687102080⟩, ⟨.hall 3 37, 905369872571333417888640⟩, ⟨.assumptionRow 21, 122818292980533696⟩]
  caps := #[0, 7474733471959761870720, 3684542187165457812480, 8372289125011705738416, 8048209794548541805044, 1189987299905196380928, 106434497071786976016, 1748942811940960796352, 515073782053906991787, 8433426716484665376, 301177866957004343904, 922950037688363458800, 0, 0, 124780551728886553294080, 43194845003545985692800] }

theorem case_56_41_21_checked :
    (Witness.linear .conditional case_56_41_21).check 56 41 21 = true := by
  change case_56_41_21.check 56 41 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_41_22 : Certificate := {
  objectiveScale := 1260225607305600000
  eta := 24388586221444277941912003200
  rows := #[⟨.count 2, 1854945352662171702620688000⟩, ⟨.count 3, 121036591278474027213657600⟩, ⟨.count 4, 5981202814818829572374400⟩, ⟨.count 5, 160515338874708609792000⟩, ⟨.path 4, 2170073970046810277049600⟩, ⟨.path 5, 149561662442491995696000⟩, ⟨.privateRow 2 38, 146258065509596600991631200⟩, ⟨.privateRow 2 39, 232119225104980186762588800⟩, ⟨.privateRow 3 33, 724659873628111577956800⟩, ⟨.privateRow 3 34, 13789872762726216667230720⟩, ⟨.privateRow 3 35, 26347088044981467904140000⟩, ⟨.privateRow 3 36, 56979601230961666713456000⟩, ⟨.privateRow 3 37, 70891599414015057514636800⟩, ⟨.privateRow 3 38, 110398437194552714099692800⟩, ⟨.privateRow 4 30, 1013190375342350166261300⟩, ⟨.privateRow 4 31, 3164803545268529353332000⟩, ⟨.privateRow 4 32, 5307121993284050655315600⟩, ⟨.privateRow 4 33, 12261465770378600623367520⟩, ⟨.privateRow 4 34, 18350539909025574216166200⟩, ⟨.privateRow 4 35, 25753014087667051559774400⟩, ⟨.privateRow 4 36, 38163274233112947174656400⟩, ⟨.privateRow 5 26, 29184607068128838144000⟩, ⟨.privateRow 5 27, 284513438155421010856320⟩, ⟨.privateRow 5 28, 636264968261692183814400⟩, ⟨.privateRow 5 29, 1163234596407653956586400⟩, ⟨.privateRow 5 30, 2672867026797603189840000⟩, ⟨.privateRow 5 31, 4565658170117493019771200⟩, ⟨.privateRow 5 32, 6833940552590719061894400⟩, ⟨.privateRow 5 33, 9589286666461889041855200⟩, ⟨.privateRow 5 34, 15097805248990300656019200⟩, ⟨.privateRow 5 35, 13665874663445504266166400⟩, ⟨.privateRow 6 23, 10109379515666744174400⟩, ⟨.privateRow 6 24, 68302620760748403229200⟩, ⟨.privateRow 6 25, 147838275179490145723200⟩, ⟨.privateRow 6 26, 263947410362098970226720⟩, ⟨.privateRow 6 27, 637268189129659112625600⟩, ⟨.privateRow 6 28, 1166369661620050609121400⟩, ⟨.privateRow 6 29, 1881899031039106031409600⟩, ⟨.privateRow 6 30, 2818214621597097518796000⟩, ⟨.privateRow 6 31, 3936036753381448497862080⟩, ⟨.privateRow 6 32, 6258091774377701924265600⟩, ⟨.privateRow 6 33, 5501997646886626576891200⟩, ⟨.privateRow 7 20, 3076543995098581687680⟩, ⟨.privateRow 7 21, 17723568667415742331200⟩, ⟨.privateRow 7 22, 41260673646639841363200⟩, ⟨.privateRow 7 23, 73067919883591315082400⟩, ⟨.privateRow 7 24, 167507484318114477264000⟩, ⟨.privateRow 7 25, 334072549032987294129600⟩, ⟨.privateRow 7 26, 569457889720783368905600⟩, ⟨.privateRow 7 27, 891278139449619004683600⟩, ⟨.privateRow 7 28, 1314983695793222974147200⟩, ⟨.privateRow 7 29, 1830655146068985762926400⟩, ⟨.privateRow 7 30, 2924723237079586460918400⟩, ⟨.privateRow 7 31, 688209515425313164483200⟩, ⟨.privateRow 8 17, 1101575855022510067200⟩, ⟨.privateRow 8 18, 5522939882505436215825⟩, ⟨.privateRow 8 19, 14045092151537003356800⟩, ⟨.privateRow 8 20, 26209145175636015192600⟩, ⟨.privateRow 8 21, 56765580779128721900400⟩, ⟨.privateRow 8 22, 110702636055517352847000⟩, ⟨.privateRow 8 23, 203175026237575059922800⟩, ⟨.privateRow 8 24, 330761920168696429052640⟩, ⟨.privateRow 8 25, 502827303739979847028400⟩, ⟨.privateRow 8 26, 727052973406907689391850⟩, ⟨.privateRow 8 27, 1002468452315953614591600⟩, ⟨.privateRow 8 28, 373853043172509262962600⟩, ⟨.privateRow 9 14, 457609518721757001600⟩, ⟨.privateRow 9 15, 2192223378149955550400⟩, ⟨.privateRow 9 16, 5940641218157107862400⟩, ⟨.privateRow 9 17, 11996849546104523700600⟩, ⟨.privateRow 9 18, 26306680537799466604800⟩, ⟨.privateRow 9 19, 49157822530379511748800⟩, ⟨.privateRow 9 20, 88900803069069383884800⟩, ⟨.privateRow 9 21, 152322368452978691167200⟩, ⟨.privateRow 9 22, 239374579223381741193600⟩, ⟨.privateRow 9 23, 353802559436336894083200⟩, ⟨.privateRow 9 24, 297622190830188880656000⟩, ⟨.privateRow 10 11, 238862111420697336000⟩, ⟨.privateRow 10 12, 1103542954763621692320⟩, ⟨.privateRow 10 13, 3168065898842933088000⟩, ⟨.privateRow 10 14, 6911077090438842921600⟩, ⟨.privateRow 10 15, 15992520895237512225600⟩, ⟨.privateRow 10 16, 30660937777239261792300⟩, ⟨.privateRow 10 17, 42870971757786757865280⟩, ⟨.privateRow 10 18, 112575713112574654456800⟩, ⟨.privateRow 10 19, 136669550551494686510400⟩, ⟨.privateRow 10 20, 91961912896968474360000⟩, ⟨.privateRow 11 8, 174473194429031097600⟩, ⟨.privateRow 11 9, 729615176703220953600⟩, ⟨.privateRow 11 10, 2197531425070415491200⟩, ⟨.privateRow 11 11, 5116426426631336937120⟩, ⟨.privateRow 11 12, 12461059202115536812800⟩, ⟨.privateRow 11 13, 25526397640491855307200⟩, ⟨.privateRow 11 14, 46148159926478725315200⟩, ⟨.privateRow 11 15, 63704525115899979511200⟩, ⟨.privateRow 12 6, 689714346727263557700⟩, ⟨.privateRow 12 7, 1919205138719342073600⟩, ⟨.privateRow 12 8, 2508052169917322028000⟩, ⟨.privateRow 12 9, 17866885934268160732800⟩, ⟨.privateRow 12 10, 25381487959563298923360⟩, ⟨.privateRow 12 11, 6388932895999915060800⟩, ⟨.privateRow 13 3, 848879195972016686400⟩, ⟨.privateRow 13 4, 2648503091432692061568⟩, ⟨.privateRow 13 5, 6437333902787793205200⟩, ⟨.privateRow 13 6, 8636423124237039331200⟩, ⟨.privateRow 14 1, 5313354967380400740800⟩, ⟨.hall 4 36, 1029575751309195157267200⟩, ⟨.hall 3 37, 10883256782295128037206400⟩, ⟨.assumptionRow 22, 685080879406747200⟩]
  caps := #[0, 1411467033377452608648000, 236922209403829216581600, 0, 17153557127842944297060, 3031174266578130816000, 4154627812228843506600, 2272486244276602613280, 7645825824982113600, 3980474724761568145600, 2931648007342757976000, 4124940558579156014400, 3259327034621251894608, 2696678344052881727616, 256728393717881955584000, 846922524559789659696000] }

theorem case_56_41_22_checked :
    (Witness.linear .conditional case_56_41_22).check 56 41 22 = true := by
  change case_56_41_22.check 56 41 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_41_23 : Certificate := {
  objectiveScale := 1248872223456000000
  eta := 38688737246453193279671491200
  rows := #[⟨.count 2, 3034765196459054926313846400⟩, ⟨.count 3, 206914304018179067310000000⟩, ⟨.count 4, 10991287829445672055507200⟩, ⟨.count 5, 341095095108755795808000⟩, ⟨.path 4, 2598489790774996332614400⟩, ⟨.path 5, 341685361909840404456000⟩, ⟨.privateRow 2 38, 247110856145443987452756000⟩, ⟨.privateRow 2 39, 403698083711628087484502400⟩, ⟨.privateRow 3 34, 23536364139198523453800960⟩, ⟨.privateRow 3 35, 42977480373269246807402400⟩, ⟨.privateRow 3 36, 95897882768958725062608000⟩, ⟨.privateRow 3 37, 122747082858357640836753600⟩, ⟨.privateRow 3 38, 199652991375834436574534400⟩, ⟨.privateRow 4 30, 1487713845890707493958900⟩, ⟨.privateRow 4 31, 5248923239836397749399200⟩, ⟨.privateRow 4 32, 8710632389600853891379200⟩, ⟨.privateRow 4 33, 20029304628959733715608000⟩, ⟨.privateRow 4 34, 30500547840973049048609400⟩, ⟨.privateRow 4 35, 42600436530391676062526400⟩, ⟨.privateRow 4 36, 59083689798044305406812800⟩, ⟨.privateRow 5 25, 3344069559889762704000⟩, ⟨.privateRow 5 26, 68219019021751159161600⟩, ⟨.privateRow 5 27, 447837795460437021319680⟩, ⟨.privateRow 5 28, 1038222129360441660835200⟩, ⟨.privateRow 5 29, 1902608376099280490440800⟩, ⟨.privateRow 5 30, 4339646840291229200448000⟩, ⟨.privateRow 5 31, 7418483911659449582553600⟩, ⟨.privateRow 5 32, 11285030899586388811426560⟩, ⟨.privateRow 5 33, 16262711880177899493957600⟩, ⟨.privateRow 5 34, 26472323449999339517404800⟩, ⟨.privateRow 5 35, 26610433522822786717080000⟩, ⟨.privateRow 6 20, 125402608495866101400⟩, ⟨.privateRow 6 21, 468169738384566778560⟩, ⟨.privateRow 6 22, 3152979870753204835200⟩, ⟨.privateRow 6 23, 26469596747127429403200⟩, ⟨.privateRow 6 24, 114367178948229884476800⟩, ⟨.privateRow 6 25, 242049834871293551356800⟩, ⟨.privateRow 6 26, 431485295312576081697120⟩, ⟨.privateRow 6 27, 1034209245888573945590400⟩, ⟨.privateRow 6 28, 1876524633532140341349600⟩, ⟨.privateRow 6 29, 3035173077400516909084800⟩, ⟨.privateRow 6 30, 4606455818748148124760000⟩, ⟨.privateRow 6 31, 6590358525848348746535040⟩, ⟨.privateRow 6 32, 8461164800433077593660800⟩, ⟨.privateRow 6 33, 17275797753346503105134400⟩, ⟨.privateRow 7 17, 37156328443219585600⟩, ⟨.privateRow 7 18, 275393963755627516800⟩, ⟨.privateRow 7 19, 1504831301950393216800⟩, ⟨.privateRow 7 20, 9586332738350653084800⟩, ⟨.privateRow 7 21, 32771881686919674499200⟩, ⟨.privateRow 7 22, 69710988517701976368000⟩, ⟨.privateRow 7 23, 120888114590014921749600⟩, ⟨.privateRow 7 24, 273727293793158394425600⟩, ⟨.privateRow 7 25, 538997131663031952630720⟩, ⟨.privateRow 7 26, 910478672172652725542400⟩, ⟨.privateRow 7 27, 1426496472509975525458800⟩, ⟨.privateRow 7 28, 2126541605556184242940800⟩, ⟨.privateRow 7 29, 3021478316345730261820800⟩, ⟨.privateRow 7 30, 5006607182284557129920640⟩, ⟨.privateRow 7 31, 5105892607517684184602400⟩, ⟨.privateRow 8 14, 29260608649035423660⟩, ⟨.privateRow 8 15, 184803844099171096800⟩, ⟨.privateRow 8 16, 780282897307611297600⟩, ⟨.privateRow 8 17, 3993212474456598993600⟩, ⟨.privateRow 8 18, 11887122263670640861875⟩, ⟨.privateRow 8 19, 25476236597093508866640⟩, ⟨.privateRow 8 20, 44810532102522820233600⟩, ⟨.privateRow 8 21, 94264176170892580221600⟩, ⟨.privateRow 8 22, 180781793769957192512700⟩, ⟨.privateRow 8 23, 327027202482946816796400⟩, ⟨.privateRow 8 24, 527217646638320263505880⟩, ⟨.privateRow 8 25, 800115087614179751414000⟩, ⟨.privateRow 8 26, 1164645375753232450227150⟩, ⟨.privateRow 8 27, 1630651919141245538538000⟩, ⟨.privateRow 8 28, 2683587954565202155270800⟩, ⟨.privateRow 8 30, 967940934110091814672800⟩, ⟨.privateRow 9 11, 30400632362634206400⟩, ⟨.privateRow 9 12, 127393126091038579200⟩, ⟨.privateRow 9 13, 501610433983464405600⟩, ⟨.privateRow 9 14, 2041642468143223545600⟩, ⟨.privateRow 9 15, 5684918251812596596800⟩, ⟨.privateRow 9 16, 12117334405247610739200⟩, ⟨.privateRow 9 17, 21903655617277945711200⟩, ⟨.privateRow 9 18, 45078057667314001249920⟩, ⟨.privateRow 9 19, 81786386950446767846400⟩, ⟨.privateRow 9 20, 145338407795208917520000⟩, ⟨.privateRow 9 21, 245454705695908582473600⟩, ⟨.privateRow 9 22, 381649538680509827145600⟩, ⟨.privateRow 9 23, 561603041887886748509760⟩, ⟨.privateRow 9 25, 2686123873981451891988000⟩, ⟨.privateRow 10 8, 41800869498622033800⟩, ⟨.privateRow 10 9, 87236597214515548800⟩, ⟨.privateRow 10 10, 319206639807659167200⟩, ⟨.privateRow 10 11, 1194310557103486680000⟩, ⟨.privateRow 10 12, 3210306777494172195840⟩, ⟨.privateRow 10 13, 6969744977454452793600⟩, ⟨.privateRow 10 14, 12763198820245927653600⟩, ⟨.privateRow 10 15, 26791898473940334134400⟩, ⟨.privateRow 10 16, 48656212096396047343200⟩, ⟨.privateRow 10 17, 83133569258859500821440⟩, ⟨.privateRow 10 18, 139232724747124477154400⟩, ⟨.privateRow 10 19, 223409570212635300648000⟩, ⟨.privateRow 10 20, 337500220331874300901200⟩, ⟨.privateRow 10 22, 1248408048098046212657280⟩, ⟨.privateRow 11 6, 80257669437354304896⟩, ⟨.privateRow 11 7, 334406955988976270400⟩, ⟨.privateRow 11 8, 1046839166574186585600⟩, ⟨.privateRow 11 9, 2736056912637078576000⟩, ⟨.privateRow 11 10, 6019325207801572867200⟩, ⟨.privateRow 11 11, 11436717894822988447680⟩, ⟨.privateRow 11 12, 23760494241321998160000⟩, ⟨.privateRow 11 13, 44364656161204185206400⟩, ⟨.privateRow 11 14, 76244785965486589651200⟩, ⟨.privateRow 11 15, 124148582410907440386000⟩, ⟨.privateRow 11 17, 698385041371834870996800⟩, ⟨.privateRow 11 18, 250033508631757642176000⟩, ⟨.privateRow 11 19, 438073112345558914224000⟩, ⟨.privateRow 11 21, 1953070385758017009644160⟩, ⟨.privateRow 12 1, 190266026683383050400⟩, ⟨.privateRow 12 3, 204359806437707720800⟩, ⟨.privateRow 12 4, 424439597986008343200⟩, ⟨.privateRow 12 5, 1324251545716346030784⟩, ⟨.privateRow 12 6, 3218666951393896602600⟩, ⟨.privateRow 12 7, 6957118627857615016800⟩, ⟨.privateRow 12 8, 13543481717553538951200⟩, ⟨.privateRow 12 9, 28639567159341610586400⟩, ⟨.privateRow 12 11, 201541792264724593281600⟩, ⟨.privateRow 12 12, 102077723315635006539600⟩, ⟨.privateRow 12 14, 611086911200355512122200⟩, ⟨.privateRow 12 18, 5476331913014472648138000⟩, ⟨.privateRow 13 4, 38844712007679483569664⟩, ⟨.privateRow 13 5, 6437333902787793205200⟩, ⟨.privateRow 13 6, 49899333606702893913600⟩, ⟨.privateRow 13 7, 95305982456858237064000⟩, ⟨.privateRow 13 9, 556185649200865332929280⟩, ⟨.privateRow 13 11, 996867135803138262062400⟩, ⟨.privateRow 13 16, 9655151974985717791113600⟩, ⟨.privateRow 13 18, 13507365766306729513996800⟩, ⟨.privateRow 14 1, 21253419869521602963200⟩, ⟨.privateRow 14 4, 11955048676605901666800⟩, ⟨.privateRow 14 6, 6520935641785037272800⟩, ⟨.privateRow 14 7, 6831456386631943809600⟩, ⟨.privateRow 14 8, 1147684672954166560012800⟩, ⟨.privateRow 14 14, 67201036475298431255035200⟩, ⟨.privateRow 14 22, 147716581448142520994980800⟩, ⟨.privateRow 15 0, 371934847716628051856000⟩, ⟨.privateRow 15 6, 8033792710679165920089600⟩, ⟨.privateRow 15 9, 10934884522868864724566400⟩, ⟨.privateRow 15 26, 22687430614957964558333030400⟩, ⟨.hall 14 3, 13732978992613958837760⟩, ⟨.hall 9 8, 804613981553008704⟩, ⟨.hall 11 21, 1110704686020357120⟩, ⟨.hall 12 26, 2766407626063156732800⟩, ⟨.hall 3 32, 68094989005967352000⟩, ⟨.hall 7 32, 763592354049694478400⟩, ⟨.hall 5 33, 71190276344992147200⟩]
  caps := #[0, 420250801384147278916800, 224762482792157702277600, 24026483726289510523200, 12234637192355218572360, 986273831913115680000, 0, 12804814847590109432160, 37240774644226902840, 1044837040271502229200, 0, 43327326725134766403360, 5772179148983399957024, 179183658210208225979328, 300924472187093093253200, 0] }

theorem case_56_41_23_checked :
    (Witness.linear .conditional case_56_41_23).check 56 41 23 = true := by
  change case_56_41_23.check 56 41 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_41_24 : Certificate := {
  objectiveScale := 5
  eta := 32957340
  rows := #[⟨.assumptionRow 24, 3⟩]
  caps := #[0, 0, 11219520, 4942470, 1776060, 740025, 284625, 110561, 46398, 16473, 7752, 28514250, 27943965, 19684665, 11759670, 6249100] }

theorem case_56_41_24_checked :
    (Witness.linear .conditional case_56_41_24).check 56 41 24 = true := by
  change case_56_41_24.check 56 41 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_41_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9694845, 9694845, 7020405, 4345965, 2414425] }

theorem case_56_41_25_checked :
    (Witness.linear .negative case_56_41_25).check 56 41 25 = true := by
  change case_56_41_25.check 56 41 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_41_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2674440, 2674440, 1931540] }

theorem case_56_41_26_checked :
    (Witness.linear .negative case_56_41_26).check 56 41 26 = true := by
  change case_56_41_26.check 56 41 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_42_1_checked :
    (Witness.rising).check 56 42 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_42_2_checked :
    (Witness.rising).check 56 42 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_42_3_checked :
    (Witness.rising).check 56 42 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_42_4_checked :
    (Witness.rising).check 56 42 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_42_5_checked :
    (Witness.rising).check 56 42 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_42_6_checked :
    (Witness.rising).check 56 42 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_42_7_checked :
    (Witness.rising).check 56 42 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_42_8_checked :
    (Witness.rising).check 56 42 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_42_9_checked :
    (Witness.rising).check 56 42 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_42_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_56_42_10_checked :
    (Witness.linear .positive case_56_42_10).check 56 42 10 = true := by
  change case_56_42_10.check 56 42 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_42_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_56_42_11_checked :
    (Witness.linear .positive case_56_42_11).check 56 42 11 = true := by
  change case_56_42_11.check 56 42 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_42_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_56_42_12_checked :
    (Witness.linear .positive case_56_42_12).check 56 42 12 = true := by
  change case_56_42_12.check 56 42 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_42_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_56_42_13_checked :
    (Witness.linear .positive case_56_42_13).check 56 42 13 = true := by
  change case_56_42_13.check 56 42 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_42_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_56_42_14_checked :
    (Witness.linear .positive case_56_42_14).check 56 42 14 = true := by
  change case_56_42_14.check 56 42 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_42_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_56_42_15_checked :
    (Witness.linear .positive case_56_42_15).check 56 42 15 = true := by
  change case_56_42_15.check 56 42 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_42_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_56_42_16_checked :
    (Witness.linear .positive case_56_42_16).check 56 42 16 = true := by
  change case_56_42_16.check 56 42 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_42_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_56_42_17_checked :
    (Witness.linear .positive case_56_42_17).check 56 42 17 = true := by
  change case_56_42_17.check 56 42 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_42_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_56_42_18_checked :
    (Witness.linear .positive case_56_42_18).check 56 42 18 = true := by
  change case_56_42_18.check 56 42 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_42_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_56_42_19_checked :
    (Witness.linear .positive case_56_42_19).check 56 42 19 = true := by
  change case_56_42_19.check 56 42 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_42_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_56_42_20_checked :
    (Witness.linear .positive case_56_42_20).check 56 42 20 = true := by
  change case_56_42_20.check 56 42 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_42_21 : Certificate := {
  objectiveScale := 2
  eta := 579989850
  rows := #[⟨.assumptionRow 21, 3⟩]
  caps := #[0, 0, 163761840, 46523250, 13306650, 3834675, 1114350, 326876, 96900, 29070, 9282, 8064030, 6113055, 3251625, 1426230] }

theorem case_56_42_21_checked :
    (Witness.linear .conditional case_56_42_21).check 56 42 21 = true := by
  change case_56_42_21.check 56 42 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_42_22 : Certificate := {
  objectiveScale := 82802264480000000
  eta := 5188699354343285040171912000
  rows := #[⟨.count 2, 253965046210568512131312000⟩, ⟨.count 3, 8448469519770195751836000⟩, ⟨.count 4, 80087871075648836400000⟩, ⟨.path 2, 9835991886155811842466000⟩, ⟨.path 3, 6379742587090281160752000⟩, ⟨.path 4, 73265524050263920502400⟩, ⟨.privateRow 2 39, 17733857292280921844052000⟩, ⟨.privateRow 2 40, 25988514164048047411800000⟩, ⟨.privateRow 3 34, 929419743832904746422000⟩, ⟨.privateRow 3 35, 1824188135447078762961600⟩, ⟨.privateRow 3 36, 3289676044324838995827000⟩, ⟨.privateRow 3 37, 6871539338290670163120000⟩, ⟨.privateRow 3 38, 7778934917577771479532000⟩, ⟨.privateRow 3 39, 11094305820539381143704000⟩, ⟨.privateRow 4 29, 19861792026760911427200⟩, ⟨.privateRow 4 30, 53480900573849945196000⟩, ⟨.privateRow 4 31, 296124903302211572589000⟩, ⟨.privateRow 4 32, 439453589716524543732000⟩, ⟨.privateRow 4 33, 705707623961592330078000⟩, ⟨.privateRow 4 34, 1574047018120802230605600⟩, ⟨.privateRow 4 35, 2223639740415389942646000⟩, ⟨.privateRow 4 36, 2920003779418156575144000⟩, ⟨.privateRow 4 37, 3955139513070917785614000⟩, ⟨.privateRow 5 25, 1872824062076711251200⟩, ⟨.privateRow 5 26, 5445975233144120875200⟩, ⟨.privateRow 5 27, 21405303723855234456000⟩, ⟨.privateRow 5 28, 74353579506632379713760⟩, ⟨.privateRow 5 29, 110521262084395394232000⟩, ⟨.privateRow 5 30, 168865276163005571549400⟩, ⟨.privateRow 5 31, 372934892225978495899200⟩, ⟨.privateRow 5 32, 607599981893922505488000⟩, ⟨.privateRow 5 33, 859438962087002793175680⟩, ⟨.privateRow 5 34, 1130039860877405081604000⟩, ⟨.privateRow 5 35, 1642121708535103741545600⟩, ⟨.privateRow 5 36, 720470488196536932254400⟩, ⟨.privateRow 6 21, 144603100553254843500⟩, ⟨.privateRow 6 22, 569513749871280614400⟩, ⟨.privateRow 6 23, 2428060853245861548000⟩, ⟨.privateRow 6 24, 7461177732688652280000⟩, ⟨.privateRow 6 25, 20318589513636834420000⟩, ⟨.privateRow 6 26, 33102986711268185712000⟩, ⟨.privateRow 6 27, 47714573856403228975200⟩, ⟨.privateRow 6 28, 99328734916786198824000⟩, ⟨.privateRow 6 29, 173190021201090608715000⟩, ⟨.privateRow 6 30, 265637484761390172288000⟩, ⟨.privateRow 6 31, 376650291451329231336000⟩, ⟨.privateRow 6 32, 494159961841436798107200⟩, ⟨.privateRow 6 33, 676698017327523973782000⟩, ⟨.privateRow 7 17, 14050503697482252000⟩, ⟨.privateRow 7 18, 66739892563040697000⟩, ⟨.privateRow 7 19, 345477090914563608000⟩, ⟨.privateRow 7 20, 1192975579564352458875⟩, ⟨.privateRow 7 21, 3087832362583349581200⟩, ⟨.privateRow 7 22, 7007688719119273185000⟩, ⟨.privateRow 7 23, 12126125094915548178000⟩, ⟨.privateRow 7 24, 17775058052623172301000⟩, ⟨.privateRow 7 25, 33054448607585974296000⟩, ⟨.privateRow 7 26, 57062608141399795935000⟩, ⟨.privateRow 7 27, 92442166743429480978000⟩, ⟨.privateRow 7 28, 137384068841019274774500⟩, ⟨.privateRow 7 29, 192058342255698828624000⟩, ⟨.privateRow 7 30, 252388027042565569155000⟩, ⟨.privateRow 7 31, 22531387729282539307200⟩, ⟨.privateRow 8 14, 12712360488198228000⟩, ⟨.privateRow 8 15, 53391914050432557600⟩, ⟨.privateRow 8 16, 245883814705939410000⟩, ⟨.privateRow 8 17, 726723274575332034000⟩, ⟨.privateRow 8 18, 1656719685976657302000⟩, ⟨.privateRow 8 19, 3320309655011274675750⟩, ⟨.privateRow 8 20, 5748529412763238701600⟩, ⟨.privateRow 8 21, 8752460196124479978000⟩, ⟨.privateRow 8 22, 15586331832414735084000⟩, ⟨.privateRow 8 23, 24582527094053323395000⟩, ⟨.privateRow 8 24, 39619227130605068310000⟩, ⟨.privateRow 8 25, 60679910318316601712400⟩, ⟨.privateRow 8 26, 87666556653363013326000⟩, ⟨.privateRow 8 27, 54109367895485245092750⟩, ⟨.privateRow 9 11, 15475917116067408000⟩, ⟨.privateRow 9 12, 56627787629246652000⟩, ⟨.privateRow 9 13, 211872674803303800000⟩, ⟨.privateRow 9 14, 569513749871280614400⟩, ⟨.privateRow 9 15, 1189609313053497336000⟩, ⟨.privateRow 9 16, 2204888302453048212000⟩, ⟨.privateRow 9 17, 3716495978020305480000⟩, ⟨.privateRow 9 18, 5750754075848673391500⟩, ⟨.privateRow 9 19, 10239382627894066046400⟩, ⟨.privateRow 9 20, 15687052842436613352000⟩, ⟨.privateRow 9 21, 23382920307215079072000⟩, ⟨.privateRow 9 22, 35342480883939106878000⟩, ⟨.privateRow 9 23, 8219118890187799776000⟩, ⟨.privateRow 10 8, 12814059372103813824⟩, ⟨.privateRow 10 9, 66739892563040697000⟩, ⟨.privateRow 10 10, 236781531875831342400⟩, ⟨.privateRow 10 11, 582457244186536992000⟩, ⟨.privateRow 10 12, 1159367276523678393600⟩, ⟨.privateRow 10 13, 2066267073751739979120⟩, ⟨.privateRow 10 14, 3388981491832719182400⟩, ⟨.privateRow 10 15, 5196812967575435606400⟩, ⟨.privateRow 10 16, 9195972019980384038400⟩, ⟨.privateRow 10 17, 14335728922541141715600⟩, ⟨.privateRow 10 18, 491205609263979529920⟩, ⟨.privateRow 11 5, 29662174472462532000⟩, ⟨.privateRow 11 6, 123212109347152056000⟩, ⟨.privateRow 11 7, 352386632732854880160⟩, ⟨.privateRow 11 8, 800878710756488364000⟩, ⟨.privateRow 11 9, 1601757421512976728000⟩, ⟨.privateRow 11 10, 2803075487647709274000⟩, ⟨.privateRow 11 11, 4462038531357578028000⟩, ⟨.privateRow 11 12, 2442680067807289510200⟩, ⟨.privateRow 12 2, 101260526647372092000⟩, ⟨.privateRow 12 3, 209753948055270762000⟩, ⟨.privateRow 12 5, 3162444139910236104000⟩, ⟨.privateRow 12 6, 822235476376661387040⟩, ⟨.privateRow 13 0, 1174622109109516267200⟩, ⟨.hall 3 38, 673374712933743844716000⟩, ⟨.assumptionRow 22, 52861905561628800⟩]
  caps := #[0, 44881845727019413023600, 0, 4541551492750983874800, 0, 438101627745681973700, 191558053573262028000, 276746383022232753450, 1308633912647682569700, 0, 6211543867160874815976, 96146358634878552000, 0, 82736650672702256630400, 212839085970866282928000] }

theorem case_56_42_22_checked :
    (Witness.linear .conditional case_56_42_22).check 56 42 22 = true := by
  change case_56_42_22.check 56 42 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_42_23 : Certificate := {
  objectiveScale := 214869229579620000000
  eta := 21080023709433457157817363936000
  rows := #[⟨.count 2, 1010373842118592957610548944000⟩, ⟨.count 3, 34879872013502713498393092000⟩, ⟨.count 4, 594943962587407972034496000⟩, ⟨.path 2, 112247697033344205479513367000⟩, ⟨.path 3, 18531022987239081027400692000⟩, ⟨.path 4, 593557354742206298827219200⟩, ⟨.path 5, 2936555272773790668000⟩, ⟨.privateRow 2 39, 71254797174369473754097008000⟩, ⟨.privateRow 2 40, 105274308414389103741207456000⟩, ⟨.privateRow 3 34, 3697670755980574762971582000⟩, ⟨.privateRow 3 35, 7220448502269506320370954400⟩, ⟨.privateRow 3 36, 13064084695716493480746705000⟩, ⟨.privateRow 3 37, 27555051876417226555341948000⟩, ⟨.privateRow 3 38, 31593575944296837135624960000⟩, ⟨.privateRow 3 39, 45641433819528823647715344000⟩, ⟨.privateRow 4 29, 94242200970203633501154000⟩, ⟨.privateRow 4 30, 228232813233962540995992000⟩, ⟨.privateRow 4 31, 1186361856431032814924391000⟩, ⟨.privateRow 4 32, 1736840718366318470083464000⟩, ⟨.privateRow 4 33, 2772772239429460645527150000⟩, ⟨.privateRow 4 34, 6218446615854334445631247200⟩, ⟨.privateRow 4 35, 8880564407069800892911464000⟩, ⟨.privateRow 4 36, 11834768910952102547151720000⟩, ⟨.privateRow 4 37, 16361600074561679799884022000⟩, ⟨.privateRow 5 22, 64110340796056893538200⟩, ⟨.privateRow 5 23, 239345272305279069209280⟩, ⟨.privateRow 5 24, 915862011372241336260000⟩, ⟨.privateRow 5 25, 12585353054733630177652800⟩, ⟨.privateRow 5 26, 28336770631857146943884400⟩, ⟨.privateRow 5 27, 94183918842207218143392000⟩, ⟨.privateRow 5 28, 301369890014104245144370560⟩, ⟨.privateRow 5 29, 439711457406555547147334400⟩, ⟨.privateRow 5 30, 661875158378491368888376800⟩, ⟨.privateRow 5 31, 1454755218863668138515384000⟩, ⟨.privateRow 5 32, 2383280548979816331651405600⟩, ⟨.privateRow 5 33, 3409234058716395061816984320⟩, ⟨.privateRow 5 34, 4561707189002632202817082800⟩, ⟨.privateRow 5 35, 6800483029828136296433385600⟩, ⟨.privateRow 5 36, 3567355803255789784039600800⟩, ⟨.privateRow 6 18, 14996570946446056968000⟩, ⟨.privateRow 6 19, 79148568884020856220000⟩, ⟨.privateRow 6 20, 234652227750273597264000⟩, ⟨.privateRow 6 21, 1656183803898136416403500⟩, ⟨.privateRow 6 22, 4406992315462281274329600⟩, ⟨.privateRow 6 23, 13351232876893118146368000⟩, ⟨.privateRow 6 24, 33863410779455692484280000⟩, ⟨.privateRow 6 25, 84459437856138655672362000⟩, ⟨.privateRow 6 26, 133893475383764881898568000⟩, ⟨.privateRow 6 27, 189196739060363454708288000⟩, ⟨.privateRow 6 28, 386719907567325903490920000⟩, ⟨.privateRow 6 29, 670594164726755106409572000⟩, ⟨.privateRow 6 30, 1033906448393552441822400000⟩, ⟨.privateRow 6 31, 1482516014052817853685576000⟩, ⟨.privateRow 6 32, 1980525141356587802690313600⟩, ⟨.privateRow 6 33, 3012259979158730952277626000⟩, ⟨.privateRow 6 34, 214555940530803737041176000⟩, ⟨.privateRow 7 14, 9713687999402559627000⟩, ⟨.privateRow 7 15, 30528733712408044542000⟩, ⟨.privateRow 7 16, 74795397595399709127900⟩, ⟨.privateRow 7 17, 292433133455698110876000⟩, ⟨.privateRow 7 18, 831059973282218990310000⟩, ⟨.privateRow 7 19, 2752973457713031310758000⟩, ⟨.privateRow 7 20, 6718229462586795302023875⟩, ⟨.privateRow 7 21, 14545923989505352956111600⟩, ⟨.privateRow 7 22, 30208182008427760074309000⟩, ⟨.privateRow 7 23, 50318398250443628492418000⟩, ⟨.privateRow 7 24, 72070708111567291152526500⟩, ⟨.privateRow 7 25, 130668530967963232102404000⟩, ⟨.privateRow 7 26, 220966974610409426394996000⟩, ⟨.privateRow 7 27, 356026092554102615448804000⟩, ⟨.privateRow 7 28, 530887047075347792574244500⟩, ⟨.privateRow 7 29, 749633056308179533728810000⟩, ⟨.privateRow 7 30, 1001652841226393342763777000⟩, ⟨.privateRow 7 31, 396415607255618458377870000⟩, ⟨.privateRow 8 11, 26712641998357038974250⟩, ⟨.privateRow 8 12, 27874061215676910234000⟩, ⟨.privateRow 8 13, 87423191994623036643000⟩, ⟨.privateRow 8 14, 213701135986856311794000⟩, ⟨.privateRow 8 15, 705213748756625828920200⟩, ⟨.privateRow 8 16, 1968299936721044977050000⟩, ⟨.privateRow 8 17, 4238405863739316850581000⟩, ⟨.privateRow 8 18, 8170925787732741333300000⟩, ⟨.privateRow 8 19, 14905654235083227747631500⟩, ⟨.privateRow 8 20, 24618370865685847118668800⟩, ⟨.privateRow 8 21, 36451308052615205183148000⟩, ⟨.privateRow 8 22, 63239097703187402420886000⟩, ⟨.privateRow 8 23, 97020315738032765554476000⟩, ⟨.privateRow 8 24, 153301424006571196033314000⟩, ⟨.privateRow 8 25, 233041088793666808011357000⟩, ⟨.privateRow 8 26, 336935457739276784928540000⟩, ⟨.privateRow 8 27, 335617634067357837672477000⟩, ⟨.privateRow 9 8, 54795163073552900460000⟩, ⟨.privateRow 9 9, 22794787838598006591360⟩, ⟨.privateRow 9 10, 83105997328221899031000⟩, ⟨.privateRow 9 11, 247769433028239202080000⟩, ⟨.privateRow 9 12, 712337119956187705980000⟩, ⟨.privateRow 9 13, 1763882392272464795760000⟩, ⟨.privateRow 9 14, 3476205145386196005182400⟩, ⟨.privateRow 9 15, 6193583800882221527784000⟩, ⟨.privateRow 9 16, 10415951665137144678552000⟩, ⟨.privateRow 9 17, 16542982056394288607112000⟩, ⟨.privateRow 9 18, 24646864350484094626908000⟩, ⟨.privateRow 9 19, 42664244571242602336828800⟩, ⟨.privateRow 9 20, 63642233545799970188556000⟩, ⟨.privateRow 9 21, 22444098794927268028416000⟩, ⟨.privateRow 9 22, 277170373374952636396818000⟩, ⟨.privateRow 10 6, 265939191450310076899200⟩, ⟨.privateRow 10 8, 348760253930549500847808⟩, ⟨.privateRow 10 9, 897544771144796509534800⟩, ⟨.privateRow 10 10, 2051530905473820593222400⟩, ⟨.privateRow 10 11, 3846620447763413612292000⟩, ⟨.privateRow 10 12, 6496514534000431878537600⟩, ⟨.privateRow 10 13, 10360231072642793995773120⟩, ⟨.privateRow 10 14, 12147222466621306144080000⟩, ⟨.privateRow 10 16, 94159234646820501050692800⟩, ⟨.privateRow 10 17, 34427253007482551830013400⟩, ⟨.privateRow 11 3, 618996393892963110024000⟩, ⟨.privateRow 11 6, 2712360572140868572770000⟩, ⟨.privateRow 11 7, 2615701904479121256358560⟩, ⟨.privateRow 11 8, 160275851990142233845500⟩, ⟨.privateRow 11 10, 51404836892838345546084000⟩, ⟨.privateRow 11 11, 122114934849632178168000⟩, ⟨.privateRow 12 2, 5998369817010380613804000⟩, ⟨.privateRow 12 3, 1511172318764198204829000⟩, ⟨.privateRow 12 4, 8009835171062910649464000⟩, ⟨.privateRow 12 5, 4520600953568114287950000⟩, ⟨.privateRow 13 0, 7522279986737342175148800⟩, ⟨.hall 3 38, 2944176989039841473456076000⟩, ⟨.assumptionRow 23, 35810168502075822400⟩]
  caps := #[0, 24655266186247933590517800, 0, 0, 4769000811560735788639800, 3330458907729459648800, 27269842688130304818400, 2323750508875523519162250, 5896436026393192549500, 3773736478292826890412480, 785670603400873296286152, 283008469589363805546600, 37686858282585903786189000, 0, 1199636764550286516445992000] }

theorem case_56_42_23_checked :
    (Witness.linear .conditional case_56_42_23).check 56 42 23 = true := by
  change case_56_42_23.check 56 42 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_42_24 : Certificate := {
  objectiveScale := 3
  eta := 59603700
  rows := #[⟨.assumptionRow 24, 2⟩]
  caps := #[0, 0, 19634160, 8064030, 2861430, 1036035, 411125, 144210, 57684, 22287, 34737360, 46523250, 36068025, 22761375, 12620790] }

theorem case_56_42_24_checked :
    (Witness.linear .conditional case_56_42_24).check 56 42 24 = true := by
  change case_56_42_24.check 56 42 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_42_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35357670, 35357670, 25662825, 15967980, 8947575] }

theorem case_56_42_25_checked :
    (Witness.linear .negative case_56_42_25).check 56 42 25 = true := by
  change case_56_42_25.check 56 42 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_42_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9694845, 9694845, 7020405] }

theorem case_56_42_26_checked :
    (Witness.linear .negative case_56_42_26).check 56 42 26 = true := by
  change case_56_42_26.check 56 42 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_42_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2674440] }

theorem case_56_42_27_checked :
    (Witness.linear .negative case_56_42_27).check 56 42 27 = true := by
  change case_56_42_27.check 56 42 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_43_1_checked :
    (Witness.rising).check 56 43 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_43_2_checked :
    (Witness.rising).check 56 43 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_43_3_checked :
    (Witness.rising).check 56 43 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_43_4_checked :
    (Witness.rising).check 56 43 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_43_5_checked :
    (Witness.rising).check 56 43 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_43_6_checked :
    (Witness.rising).check 56 43 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_43_7_checked :
    (Witness.rising).check 56 43 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_43_8_checked :
    (Witness.rising).check 56 43 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_43_9_checked :
    (Witness.rising).check 56 43 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_43_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_56_43_10_checked :
    (Witness.linear .positive case_56_43_10).check 56 43 10 = true := by
  change case_56_43_10.check 56 43 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_43_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_56_43_11_checked :
    (Witness.linear .positive case_56_43_11).check 56 43 11 = true := by
  change case_56_43_11.check 56 43 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_43_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_56_43_12_checked :
    (Witness.linear .positive case_56_43_12).check 56 43 12 = true := by
  change case_56_43_12.check 56 43 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_43_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_56_43_13_checked :
    (Witness.linear .positive case_56_43_13).check 56 43 13 = true := by
  change case_56_43_13.check 56 43 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_43_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_56_43_14_checked :
    (Witness.linear .positive case_56_43_14).check 56 43 14 = true := by
  change case_56_43_14.check 56 43 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_43_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_56_43_15_checked :
    (Witness.linear .positive case_56_43_15).check 56 43 15 = true := by
  change case_56_43_15.check 56 43 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_43_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_56_43_16_checked :
    (Witness.linear .positive case_56_43_16).check 56 43 16 = true := by
  change case_56_43_16.check 56 43 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_43_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_56_43_17_checked :
    (Witness.linear .positive case_56_43_17).check 56 43 17 = true := by
  change case_56_43_17.check 56 43 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_43_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_56_43_18_checked :
    (Witness.linear .positive case_56_43_18).check 56 43 18 = true := by
  change case_56_43_18.check 56 43 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_43_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_56_43_19_checked :
    (Witness.linear .positive case_56_43_19).check 56 43 19 = true := by
  change case_56_43_19.check 56 43 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_43_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_56_43_20_checked :
    (Witness.linear .positive case_56_43_20).check 56 43 20 = true := by
  change case_56_43_20.check 56 43 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_43_21 : Certificate := {
  objectiveScale := 19
  eta := 8351853840
  rows := #[⟨.assumptionRow 21, 32⟩]
  caps := #[0, 0, 2319959400, 660009840, 189144525, 54649035, 15935205, 4695128, 1399882, 423130, 129948, 58902480, 66966510, 38482275] }

theorem case_56_43_21_checked :
    (Witness.linear .conditional case_56_43_21).check 56 43 21 = true := by
  change case_56_43_21.check 56 43 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_43_22 : Certificate := {
  objectiveScale := 995
  eta := 353055639600
  rows := #[⟨.assumptionRow 22, 1216⟩]
  caps := #[0, 0, 102542205480, 29886535800, 8745620625, 2570936550, 759691725, 225789597, 72239596, 42181080, 21140164800, 17837634360, 10700967810, 5378838075] }

theorem case_56_43_22_checked :
    (Witness.linear .conditional case_56_43_22).check 56 43 22 = true := by
  change case_56_43_22.check 56 43 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_43_23 : Certificate := {
  objectiveScale := 1
  eta := 286097760
  rows := #[⟨.assumptionRow 23, 1⟩]
  caps := #[0, 0, 84362160, 27293640, 8684340, 2731365, 852150, 264385, 81719, 28424, 27293640, 24812400, 16128060, 8844420] }

theorem case_56_43_23_checked :
    (Witness.linear .conditional case_56_43_23).check 56 43 23 = true := by
  change case_56_43_23.check 56 43 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_43_24 : Certificate := {
  objectiveScale := 4
  eta := 256754400
  rows := #[⟨.assumptionRow 24, 3⟩]
  caps := #[0, 0, 89864040, 32256120, 10795395, 3641820, 1381380, 480700, 158631, 63954, 136468200, 131505720, 91185570, 53716845] }

theorem case_56_43_24_checked :
    (Witness.linear .conditional case_56_43_24).check 56 43 24 = true := by
  change case_56_43_24.check 56 43 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_43_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 129644790, 129644790, 94287120, 58929450, 33266625] }

theorem case_56_43_25_checked :
    (Witness.linear .negative case_56_43_25).check 56 43 25 = true := by
  change case_56_43_25.check 56 43 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_43_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35357670, 35357670, 25662825] }

theorem case_56_43_26_checked :
    (Witness.linear .negative case_56_43_26).check 56 43 26 = true := by
  change case_56_43_26.check 56 43 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_43_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9694845] }

theorem case_56_43_27_checked :
    (Witness.linear .negative case_56_43_27).check 56 43 27 = true := by
  change case_56_43_27.check 56 43 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_43_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_43_28_checked :
    (Witness.linear .negative case_56_43_28).check 56 43 28 = true := by
  change case_56_43_28.check 56 43 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_44_1_checked :
    (Witness.rising).check 56 44 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_44_2_checked :
    (Witness.rising).check 56 44 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_44_3_checked :
    (Witness.rising).check 56 44 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_44_4_checked :
    (Witness.rising).check 56 44 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_44_5_checked :
    (Witness.rising).check 56 44 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_44_6_checked :
    (Witness.rising).check 56 44 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_44_7_checked :
    (Witness.rising).check 56 44 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_44_8_checked :
    (Witness.rising).check 56 44 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_44_9_checked :
    (Witness.rising).check 56 44 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_44_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_56_44_10_checked :
    (Witness.linear .positive case_56_44_10).check 56 44 10 = true := by
  change case_56_44_10.check 56 44 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_44_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_56_44_11_checked :
    (Witness.linear .positive case_56_44_11).check 56 44 11 = true := by
  change case_56_44_11.check 56 44 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_44_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_56_44_12_checked :
    (Witness.linear .positive case_56_44_12).check 56 44 12 = true := by
  change case_56_44_12.check 56 44 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_44_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_56_44_13_checked :
    (Witness.linear .positive case_56_44_13).check 56 44 13 = true := by
  change case_56_44_13.check 56 44 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_44_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_56_44_14_checked :
    (Witness.linear .positive case_56_44_14).check 56 44 14 = true := by
  change case_56_44_14.check 56 44 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_44_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_56_44_15_checked :
    (Witness.linear .positive case_56_44_15).check 56 44 15 = true := by
  change case_56_44_15.check 56 44 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_44_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_56_44_16_checked :
    (Witness.linear .positive case_56_44_16).check 56 44 16 = true := by
  change case_56_44_16.check 56 44 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_44_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_56_44_17_checked :
    (Witness.linear .positive case_56_44_17).check 56 44 17 = true := by
  change case_56_44_17.check 56 44 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_44_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_56_44_18_checked :
    (Witness.linear .positive case_56_44_18).check 56 44 18 = true := by
  change case_56_44_18.check 56 44 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_44_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_56_44_19_checked :
    (Witness.linear .positive case_56_44_19).check 56 44 19 = true := by
  change case_56_44_19.check 56 44 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_44_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_56_44_20_checked :
    (Witness.linear .positive case_56_44_20).check 56 44 20 = true := by
  change case_56_44_20.check 56 44 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_44_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_56_44_21_checked :
    (Witness.linear .positive case_56_44_21).check 56 44 21 = true := by
  change case_56_44_21.check 56 44 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_44_22 : Certificate := {
  objectiveScale := 576
  eta := 296712261990
  rows := #[⟨.assumptionRow 22, 757⟩]
  caps := #[0, 0, 83982530280, 23884416240, 7093244850, 2123741340, 639368145, 193748320, 59164556, 18339600, 20138714760, 16459035840, 9556226160] }

theorem case_56_44_22_checked :
    (Witness.linear .conditional case_56_44_22).check 56 44 22 = true := by
  change case_56_44_22.check 56 44 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_44_23 : Certificate := {
  objectiveScale := 838
  eta := 213175842480
  rows := #[⟨.assumptionRow 23, 823⟩]
  caps := #[0, 0, 63735611880, 19187428920, 6300488670, 2029404195, 645077550, 203167855, 63577382, 83349814080, 76389935880, 50242628760, 27998312160] }

theorem case_56_44_23_checked :
    (Witness.linear .conditional case_56_44_23).check 56 44 23 = true := by
  change case_56_44_23.check 56 44 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_44_24 : Certificate := {
  objectiveScale := 537
  eta := 31420319700
  rows := #[⟨.assumptionRow 24, 398⟩]
  caps := #[0, 0, 10261006200, 3870734400, 1332515925, 434098665, 167640330, 59967325, 20470230, 66698832750, 64494871320, 45007212360, 26775060840] }

theorem case_56_44_24_checked :
    (Witness.linear .conditional case_56_44_24).check 56 44 24 = true := by
  change case_56_44_24.check 56 44 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_44_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 477638700, 477638700, 347993910, 218349120, 124062000] }

theorem case_56_44_25_checked :
    (Witness.linear .negative case_56_44_25).check 56 44 25 = true := by
  change case_56_44_25.check 56 44 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_44_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 129644790, 129644790, 94287120] }

theorem case_56_44_26_checked :
    (Witness.linear .negative case_56_44_26).check 56 44 26 = true := by
  change case_56_44_26.check 56 44 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_44_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35357670] }

theorem case_56_44_27_checked :
    (Witness.linear .negative case_56_44_27).check 56 44 27 = true := by
  change case_56_44_27.check 56 44 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_44_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_44_28_checked :
    (Witness.linear .negative case_56_44_28).check 56 44 28 = true := by
  change case_56_44_28.check 56 44 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_45_1_checked :
    (Witness.rising).check 56 45 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_45_2_checked :
    (Witness.rising).check 56 45 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_45_3_checked :
    (Witness.rising).check 56 45 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_45_4_checked :
    (Witness.rising).check 56 45 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_45_5_checked :
    (Witness.rising).check 56 45 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_45_6_checked :
    (Witness.rising).check 56 45 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_45_7_checked :
    (Witness.rising).check 56 45 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_45_8_checked :
    (Witness.rising).check 56 45 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_45_9_checked :
    (Witness.rising).check 56 45 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_45_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_56_45_10_checked :
    (Witness.linear .positive case_56_45_10).check 56 45 10 = true := by
  change case_56_45_10.check 56 45 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_45_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_56_45_11_checked :
    (Witness.linear .positive case_56_45_11).check 56 45 11 = true := by
  change case_56_45_11.check 56 45 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_45_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_56_45_12_checked :
    (Witness.linear .positive case_56_45_12).check 56 45 12 = true := by
  change case_56_45_12.check 56 45 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_45_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_56_45_13_checked :
    (Witness.linear .positive case_56_45_13).check 56 45 13 = true := by
  change case_56_45_13.check 56 45 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_45_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_56_45_14_checked :
    (Witness.linear .positive case_56_45_14).check 56 45 14 = true := by
  change case_56_45_14.check 56 45 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_45_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_56_45_15_checked :
    (Witness.linear .positive case_56_45_15).check 56 45 15 = true := by
  change case_56_45_15.check 56 45 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_45_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_56_45_16_checked :
    (Witness.linear .positive case_56_45_16).check 56 45 16 = true := by
  change case_56_45_16.check 56 45 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_45_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_56_45_17_checked :
    (Witness.linear .positive case_56_45_17).check 56 45 17 = true := by
  change case_56_45_17.check 56 45 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_45_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_56_45_18_checked :
    (Witness.linear .positive case_56_45_18).check 56 45 18 = true := by
  change case_56_45_18.check 56 45 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_45_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_56_45_19_checked :
    (Witness.linear .positive case_56_45_19).check 56 45 19 = true := by
  change case_56_45_19.check 56 45 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_45_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_56_45_20_checked :
    (Witness.linear .positive case_56_45_20).check 56 45 20 = true := by
  change case_56_45_20.check 56 45 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_45_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_56_45_21_checked :
    (Witness.linear .positive case_56_45_21).check 56 45 21 = true := by
  change case_56_45_21.check 56 45 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_45_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_56_45_22_checked :
    (Witness.linear .positive case_56_45_22).check 56 45 22 = true := by
  change case_56_45_22.check 56 45 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_45_23 : Certificate := {
  objectiveScale := 397
  eta := 209880216360
  rows := #[⟨.assumptionRow 23, 428⟩]
  caps := #[0, 0, 62259274080, 18450500640, 5466792030, 1620609900, 514187310, 165061455, 52708755, 67530075120, 60190567200, 38467311000] }

theorem case_56_45_23_checked :
    (Witness.linear .conditional case_56_45_23).check 56 45 23 = true := by
  change case_56_45_23.check 56 45 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_45_24 : Certificate := {
  objectiveScale := 641
  eta := 170082367380
  rows := #[⟨.assumptionRow 24, 553⟩]
  caps := #[0, 0, 55073818800, 17366198760, 5370643980, 1864611840, 633551100, 208095030, 68854410, 135622717470, 128314845360, 87483559920] }

theorem case_56_45_24_checked :
    (Witness.linear .conditional case_56_45_24).check 56 45 24 = true := by
  change case_56_45_24.check 56 45 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_45_25 : Certificate := {
  objectiveScale := 55
  eta := 62408580
  rows := #[⟨.assumptionRow 25, 26⟩]
  caps := #[0, 0, 29801850, 11298690, 5624190, 2072070, 1075250, 434148, 18430030410, 25690138650, 20531640690, 13455764520] }

theorem case_56_45_25_checked :
    (Witness.linear .conditional case_56_45_25).check 56 45 25 = true := by
  change case_56_45_25.check 56 45 25 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_45_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 477638700, 477638700, 347993910] }

theorem case_56_45_26_checked :
    (Witness.linear .negative case_56_45_26).check 56 45 26 = true := by
  change case_56_45_26.check 56 45 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_45_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 129644790] }

theorem case_56_45_27_checked :
    (Witness.linear .negative case_56_45_27).check 56 45 27 = true := by
  change case_56_45_27.check 56 45 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_45_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_45_28_checked :
    (Witness.linear .negative case_56_45_28).check 56 45 28 = true := by
  change case_56_45_28.check 56 45 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_45_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_45_29_checked :
    (Witness.linear .negative case_56_45_29).check 56 45 29 = true := by
  change case_56_45_29.check 56 45 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_46_1_checked :
    (Witness.rising).check 56 46 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_46_2_checked :
    (Witness.rising).check 56 46 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_46_3_checked :
    (Witness.rising).check 56 46 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_46_4_checked :
    (Witness.rising).check 56 46 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_46_5_checked :
    (Witness.rising).check 56 46 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_46_6_checked :
    (Witness.rising).check 56 46 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_46_7_checked :
    (Witness.rising).check 56 46 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_46_8_checked :
    (Witness.rising).check 56 46 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_46_9_checked :
    (Witness.rising).check 56 46 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_46_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_56_46_10_checked :
    (Witness.linear .positive case_56_46_10).check 56 46 10 = true := by
  change case_56_46_10.check 56 46 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_46_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_56_46_11_checked :
    (Witness.linear .positive case_56_46_11).check 56 46 11 = true := by
  change case_56_46_11.check 56 46 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_46_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_56_46_12_checked :
    (Witness.linear .positive case_56_46_12).check 56 46 12 = true := by
  change case_56_46_12.check 56 46 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_46_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_56_46_13_checked :
    (Witness.linear .positive case_56_46_13).check 56 46 13 = true := by
  change case_56_46_13.check 56 46 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_46_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_56_46_14_checked :
    (Witness.linear .positive case_56_46_14).check 56 46 14 = true := by
  change case_56_46_14.check 56 46 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_46_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_56_46_15_checked :
    (Witness.linear .positive case_56_46_15).check 56 46 15 = true := by
  change case_56_46_15.check 56 46 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_46_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_56_46_16_checked :
    (Witness.linear .positive case_56_46_16).check 56 46 16 = true := by
  change case_56_46_16.check 56 46 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_46_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_56_46_17_checked :
    (Witness.linear .positive case_56_46_17).check 56 46 17 = true := by
  change case_56_46_17.check 56 46 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_46_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_56_46_18_checked :
    (Witness.linear .positive case_56_46_18).check 56 46 18 = true := by
  change case_56_46_18.check 56 46 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_46_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_56_46_19_checked :
    (Witness.linear .positive case_56_46_19).check 56 46 19 = true := by
  change case_56_46_19.check 56 46 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_46_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_56_46_20_checked :
    (Witness.linear .positive case_56_46_20).check 56 46 20 = true := by
  change case_56_46_20.check 56 46 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_46_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_56_46_21_checked :
    (Witness.linear .positive case_56_46_21).check 56 46 21 = true := by
  change case_56_46_21.check 56 46 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_46_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_56_46_22_checked :
    (Witness.linear .positive case_56_46_22).check 56 46 22 = true := by
  change case_56_46_22.check 56 46 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_46_23 : Certificate := {
  objectiveScale := 63
  eta := 129572024940
  rows := #[⟨.assumptionRow 23, 85⟩]
  caps := #[0, 0, 36286274070, 10555815270, 3084181320, 905652600, 267463665, 79505595, 23809945, 7191272, 3562467300] }

theorem case_56_46_23_checked :
    (Witness.linear .conditional case_56_46_23).check 56 46 23 = true := by
  change case_56_46_23.check 56 46 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_46_24 : Certificate := {
  objectiveScale := 992
  eta := 227997907200
  rows := #[⟨.assumptionRow 24, 845⟩]
  caps := #[0, 0, 76109340000, 24514651200, 7701148650, 2541079905, 890173830, 492957660, 769298348250, 731221859520, 502178595120] }

theorem case_56_46_24_checked :
    (Witness.linear .conditional case_56_46_24).check 56 46 24 = true := by
  change case_56_46_24.check 56 46 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_46_25 : Certificate := {
  objectiveScale := 19
  eta := 209805024
  rows := #[⟨.assumptionRow 25, 11⟩]
  caps := #[0, 0, 84847620, 32957340, 12486240, 5229510, 1825395, 841225, 19187428920, 18934962750, 13571762490] }

theorem case_56_46_25_checked :
    (Witness.linear .conditional case_56_46_25).check 56 46 25 = true := by
  change case_56_46_25.check 56 46 25 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_46_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 1767263190, 1767263190, 1289624490] }

theorem case_56_46_26_checked :
    (Witness.linear .negative case_56_46_26).check 56 46 26 = true := by
  change case_56_46_26.check 56 46 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_46_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 477638700] }

theorem case_56_46_27_checked :
    (Witness.linear .negative case_56_46_27).check 56 46 27 = true := by
  change case_56_46_27.check 56 46 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_46_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_46_28_checked :
    (Witness.linear .negative case_56_46_28).check 56 46 28 = true := by
  change case_56_46_28.check 56 46 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_46_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_46_29_checked :
    (Witness.linear .negative case_56_46_29).check 56 46 29 = true := by
  change case_56_46_29.check 56 46 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_46_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_46_30_checked :
    (Witness.linear .negative case_56_46_30).check 56 46 30 = true := by
  change case_56_46_30.check 56 46 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_47_1_checked :
    (Witness.rising).check 56 47 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_47_2_checked :
    (Witness.rising).check 56 47 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_47_3_checked :
    (Witness.rising).check 56 47 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_47_4_checked :
    (Witness.rising).check 56 47 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_47_5_checked :
    (Witness.rising).check 56 47 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_47_6_checked :
    (Witness.rising).check 56 47 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_47_7_checked :
    (Witness.rising).check 56 47 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_47_8_checked :
    (Witness.rising).check 56 47 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_47_9_checked :
    (Witness.rising).check 56 47 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_47_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_56_47_10_checked :
    (Witness.linear .positive case_56_47_10).check 56 47 10 = true := by
  change case_56_47_10.check 56 47 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_47_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_56_47_11_checked :
    (Witness.linear .positive case_56_47_11).check 56 47 11 = true := by
  change case_56_47_11.check 56 47 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_47_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_56_47_12_checked :
    (Witness.linear .positive case_56_47_12).check 56 47 12 = true := by
  change case_56_47_12.check 56 47 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_47_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_56_47_13_checked :
    (Witness.linear .positive case_56_47_13).check 56 47 13 = true := by
  change case_56_47_13.check 56 47 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_47_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_56_47_14_checked :
    (Witness.linear .positive case_56_47_14).check 56 47 14 = true := by
  change case_56_47_14.check 56 47 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_47_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_56_47_15_checked :
    (Witness.linear .positive case_56_47_15).check 56 47 15 = true := by
  change case_56_47_15.check 56 47 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_47_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_56_47_16_checked :
    (Witness.linear .positive case_56_47_16).check 56 47 16 = true := by
  change case_56_47_16.check 56 47 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_47_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_56_47_17_checked :
    (Witness.linear .positive case_56_47_17).check 56 47 17 = true := by
  change case_56_47_17.check 56 47 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_47_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_56_47_18_checked :
    (Witness.linear .positive case_56_47_18).check 56 47 18 = true := by
  change case_56_47_18.check 56 47 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_47_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_56_47_19_checked :
    (Witness.linear .positive case_56_47_19).check 56 47 19 = true := by
  change case_56_47_19.check 56 47 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_47_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_56_47_20_checked :
    (Witness.linear .positive case_56_47_20).check 56 47 20 = true := by
  change case_56_47_20.check 56 47 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_47_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_56_47_21_checked :
    (Witness.linear .positive case_56_47_21).check 56 47 21 = true := by
  change case_56_47_21.check 56 47 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_47_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_56_47_22_checked :
    (Witness.linear .positive case_56_47_22).check 56 47 22 = true := by
  change case_56_47_22.check 56 47 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_47_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190, 477638700, 129644790, 35357670, 9694845, 2674440, 742900] }

theorem case_56_47_23_checked :
    (Witness.linear .positive case_56_47_23).check 56 47 23 = true := by
  change case_56_47_23.check 56 47 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_47_24 : Certificate := {
  objectiveScale := 986
  eta := 635289704370
  rows := #[⟨.assumptionRow 24, 939⟩]
  caps := #[0, 0, 198826939440, 61373471400, 18750730680, 5683970565, 1880089575, 1232394150, 1319894134650, 1226099459880] }

theorem case_56_47_24_checked :
    (Witness.linear .conditional case_56_47_24).check 56 47 24 = true := by
  change case_56_47_24.check 56 47 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_47_25 : Certificate := {
  objectiveScale := 40
  eta := 417225900
  rows := #[⟨.assumptionRow 25, 23⟩]
  caps := #[0, 0, 162683040, 65564070, 23801895, 10409685, 3700125, 149184555000, 147394340340, 105966936990] }

theorem case_56_47_25_checked :
    (Witness.linear .conditional case_56_47_25).check 56 47 25 = true := by
  change case_56_47_25.check 56 47 25 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_47_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 6564120420, 6564120420, 4796857230] }

theorem case_56_47_26_checked :
    (Witness.linear .negative case_56_47_26).check 56 47 26 = true := by
  change case_56_47_26.check 56 47 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_47_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 1767263190] }

theorem case_56_47_27_checked :
    (Witness.linear .negative case_56_47_27).check 56 47 27 = true := by
  change case_56_47_27.check 56 47 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_47_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_47_28_checked :
    (Witness.linear .negative case_56_47_28).check 56 47 28 = true := by
  change case_56_47_28.check 56 47 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_47_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_47_29_checked :
    (Witness.linear .negative case_56_47_29).check 56 47 29 = true := by
  change case_56_47_29.check 56 47 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_47_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_47_30_checked :
    (Witness.linear .negative case_56_47_30).check 56 47 30 = true := by
  change case_56_47_30.check 56 47 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_48_1_checked :
    (Witness.rising).check 56 48 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_48_2_checked :
    (Witness.rising).check 56 48 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_48_3_checked :
    (Witness.rising).check 56 48 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_48_4_checked :
    (Witness.rising).check 56 48 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_48_5_checked :
    (Witness.rising).check 56 48 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_48_6_checked :
    (Witness.rising).check 56 48 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_48_7_checked :
    (Witness.rising).check 56 48 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_48_8_checked :
    (Witness.rising).check 56 48 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_48_9_checked :
    (Witness.rising).check 56 48 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_48_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1] }

theorem case_56_48_10_checked :
    (Witness.linear .positive case_56_48_10).check 56 48 10 = true := by
  change case_56_48_10.check 56 48 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_48_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_56_48_11_checked :
    (Witness.linear .positive case_56_48_11).check 56 48 11 = true := by
  change case_56_48_11.check 56 48 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_48_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_56_48_12_checked :
    (Witness.linear .positive case_56_48_12).check 56 48 12 = true := by
  change case_56_48_12.check 56 48 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_48_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_56_48_13_checked :
    (Witness.linear .positive case_56_48_13).check 56 48 13 = true := by
  change case_56_48_13.check 56 48 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_48_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_56_48_14_checked :
    (Witness.linear .positive case_56_48_14).check 56 48 14 = true := by
  change case_56_48_14.check 56 48 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_48_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_56_48_15_checked :
    (Witness.linear .positive case_56_48_15).check 56 48 15 = true := by
  change case_56_48_15.check 56 48 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_48_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_56_48_16_checked :
    (Witness.linear .positive case_56_48_16).check 56 48 16 = true := by
  change case_56_48_16.check 56 48 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_48_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_56_48_17_checked :
    (Witness.linear .positive case_56_48_17).check 56 48 17 = true := by
  change case_56_48_17.check 56 48 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_48_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_56_48_18_checked :
    (Witness.linear .positive case_56_48_18).check 56 48 18 = true := by
  change case_56_48_18.check 56 48 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_48_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_56_48_19_checked :
    (Witness.linear .positive case_56_48_19).check 56 48 19 = true := by
  change case_56_48_19.check 56 48 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_48_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_56_48_20_checked :
    (Witness.linear .positive case_56_48_20).check 56 48 20 = true := by
  change case_56_48_20.check 56 48 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_48_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_56_48_21_checked :
    (Witness.linear .positive case_56_48_21).check 56 48 21 = true := by
  change case_56_48_21.check 56 48 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_48_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670, 9694845, 2674440, 742900] }

theorem case_56_48_22_checked :
    (Witness.linear .positive case_56_48_22).check 56 48 22 = true := by
  change case_56_48_22.check 56 48 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_48_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190, 477638700, 129644790, 35357670, 9694845, 2674440] }

theorem case_56_48_23_checked :
    (Witness.linear .positive case_56_48_23).check 56 48 23 = true := by
  change case_56_48_23.check 56 48 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_48_24 : Certificate := {
  objectiveScale := 23
  eta := 539853500550
  rows := #[⟨.assumptionRow 24, 40⟩]
  caps := #[0, 0, 149184555000, 41427403350, 11565679950, 3247943160, 918058800, 261380625, 75021975] }

theorem case_56_48_24_checked :
    (Witness.linear .conditional case_56_48_24).check 56 48 24 = true := by
  change case_56_48_24.check 56 48 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_48_25 : Certificate := {
  objectiveScale := 25
  eta := 3053543400
  rows := #[⟨.assumptionRow 25, 18⟩]
  caps := #[0, 0, 1123300500, 378658800, 129024480, 49034505, 16921905, 154243857300, 150352086300] }

theorem case_56_48_25_checked :
    (Witness.linear .conditional case_56_48_25).check 56 48 25 = true := by
  change case_56_48_25.check 56 48 25 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_48_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 24466267020, 24466267020, 17902146600] }

theorem case_56_48_26_checked :
    (Witness.linear .negative case_56_48_26).check 56 48 26 = true := by
  change case_56_48_26.check 56 48 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_48_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 6564120420] }

theorem case_56_48_27_checked :
    (Witness.linear .negative case_56_48_27).check 56 48 27 = true := by
  change case_56_48_27.check 56 48 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_48_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_48_28_checked :
    (Witness.linear .negative case_56_48_28).check 56 48 28 = true := by
  change case_56_48_28.check 56 48 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_48_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_48_29_checked :
    (Witness.linear .negative case_56_48_29).check 56 48 29 = true := by
  change case_56_48_29.check 56 48 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_48_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_48_30_checked :
    (Witness.linear .negative case_56_48_30).check 56 48 30 = true := by
  change case_56_48_30.check 56 48 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_48_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_48_31_checked :
    (Witness.linear .negative case_56_48_31).check 56 48 31 = true := by
  change case_56_48_31.check 56 48 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_49_1_checked :
    (Witness.rising).check 56 49 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_49_2_checked :
    (Witness.rising).check 56 49 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_49_3_checked :
    (Witness.rising).check 56 49 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_49_4_checked :
    (Witness.rising).check 56 49 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_49_5_checked :
    (Witness.rising).check 56 49 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_49_6_checked :
    (Witness.rising).check 56 49 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_49_7_checked :
    (Witness.rising).check 56 49 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_49_8_checked :
    (Witness.rising).check 56 49 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_49_9_checked :
    (Witness.rising).check 56 49 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_49_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2] }

theorem case_56_49_10_checked :
    (Witness.linear .positive case_56_49_10).check 56 49 10 = true := by
  change case_56_49_10.check 56 49 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_49_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5] }

theorem case_56_49_11_checked :
    (Witness.linear .positive case_56_49_11).check 56 49 11 = true := by
  change case_56_49_11.check 56 49 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_49_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14] }

theorem case_56_49_12_checked :
    (Witness.linear .positive case_56_49_12).check 56 49 12 = true := by
  change case_56_49_12.check 56 49 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_49_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42] }

theorem case_56_49_13_checked :
    (Witness.linear .positive case_56_49_13).check 56 49 13 = true := by
  change case_56_49_13.check 56 49 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_49_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_56_49_14_checked :
    (Witness.linear .positive case_56_49_14).check 56 49 14 = true := by
  change case_56_49_14.check 56 49 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_49_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_56_49_15_checked :
    (Witness.linear .positive case_56_49_15).check 56 49 15 = true := by
  change case_56_49_15.check 56 49 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_49_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_56_49_16_checked :
    (Witness.linear .positive case_56_49_16).check 56 49 16 = true := by
  change case_56_49_16.check 56 49 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_49_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_56_49_17_checked :
    (Witness.linear .positive case_56_49_17).check 56 49 17 = true := by
  change case_56_49_17.check 56 49 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_49_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_56_49_18_checked :
    (Witness.linear .positive case_56_49_18).check 56 49 18 = true := by
  change case_56_49_18.check 56 49 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_49_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_56_49_19_checked :
    (Witness.linear .positive case_56_49_19).check 56 49 19 = true := by
  change case_56_49_19.check 56 49 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_49_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_56_49_20_checked :
    (Witness.linear .positive case_56_49_20).check 56 49 20 = true := by
  change case_56_49_20.check 56 49 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_49_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900] }

theorem case_56_49_21_checked :
    (Witness.linear .positive case_56_49_21).check 56 49 21 = true := by
  change case_56_49_21.check 56 49 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_49_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670, 9694845, 2674440] }

theorem case_56_49_22_checked :
    (Witness.linear .positive case_56_49_22).check 56 49 22 = true := by
  change case_56_49_22.check 56 49 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_49_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190, 477638700, 129644790, 35357670, 9694845] }

theorem case_56_49_23_checked :
    (Witness.linear .positive case_56_49_23).check 56 49 23 = true := by
  change case_56_49_23.check 56 49 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_49_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020, 6564120420, 1767263190, 477638700, 129644790, 35357670] }

theorem case_56_49_24_checked :
    (Witness.linear .positive case_56_49_24).check 56 49 24 = true := by
  change case_56_49_24.check 56 49 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_49_25 : Certificate := {
  objectiveScale := 6
  eta := 3481039476
  rows := #[⟨.assumptionRow 25, 5⟩]
  caps := #[0, 0, 1072866600, 366792000, 124062000, 40320150, 12746370, 63293169030] }

theorem case_56_49_25_checked :
    (Witness.linear .conditional case_56_49_25).check 56 49 25 = true := by
  change case_56_49_25.check 56 49 25 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_49_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 91482563640, 91482563640, 67016296620] }

theorem case_56_49_26_checked :
    (Witness.linear .negative case_56_49_26).check 56 49 26 = true := by
  change case_56_49_26.check 56 49 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_49_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 24466267020] }

theorem case_56_49_27_checked :
    (Witness.linear .negative case_56_49_27).check 56 49 27 = true := by
  change case_56_49_27.check 56 49 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_49_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_49_28_checked :
    (Witness.linear .negative case_56_49_28).check 56 49 28 = true := by
  change case_56_49_28.check 56 49 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_49_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_49_29_checked :
    (Witness.linear .negative case_56_49_29).check 56 49 29 = true := by
  change case_56_49_29.check 56 49 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_49_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_49_30_checked :
    (Witness.linear .negative case_56_49_30).check 56 49 30 = true := by
  change case_56_49_30.check 56 49 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_49_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_49_31_checked :
    (Witness.linear .negative case_56_49_31).check 56 49 31 = true := by
  change case_56_49_31.check 56 49 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_49_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_56_49_32_checked :
    (Witness.linear .negative case_56_49_32).check 56 49 32 = true := by
  change case_56_49_32.check 56 49 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_50_1_checked :
    (Witness.rising).check 56 50 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_50_2_checked :
    (Witness.rising).check 56 50 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_50_3_checked :
    (Witness.rising).check 56 50 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_50_4_checked :
    (Witness.rising).check 56 50 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_50_5_checked :
    (Witness.rising).check 56 50 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_50_6_checked :
    (Witness.rising).check 56 50 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_50_7_checked :
    (Witness.rising).check 56 50 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_50_8_checked :
    (Witness.rising).check 56 50 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_50_9_checked :
    (Witness.rising).check 56 50 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_50_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5] }

theorem case_56_50_10_checked :
    (Witness.linear .positive case_56_50_10).check 56 50 10 = true := by
  change case_56_50_10.check 56 50 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_50_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14] }

theorem case_56_50_11_checked :
    (Witness.linear .positive case_56_50_11).check 56 50 11 = true := by
  change case_56_50_11.check 56 50 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_50_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42] }

theorem case_56_50_12_checked :
    (Witness.linear .positive case_56_50_12).check 56 50 12 = true := by
  change case_56_50_12.check 56 50 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_50_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132] }

theorem case_56_50_13_checked :
    (Witness.linear .positive case_56_50_13).check 56 50 13 = true := by
  change case_56_50_13.check 56 50 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_50_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429] }

theorem case_56_50_14_checked :
    (Witness.linear .positive case_56_50_14).check 56 50 14 = true := by
  change case_56_50_14.check 56 50 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_50_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430] }

theorem case_56_50_15_checked :
    (Witness.linear .positive case_56_50_15).check 56 50 15 = true := by
  change case_56_50_15.check 56 50 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_50_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862] }

theorem case_56_50_16_checked :
    (Witness.linear .positive case_56_50_16).check 56 50 16 = true := by
  change case_56_50_16.check 56 50 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_50_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796] }

theorem case_56_50_17_checked :
    (Witness.linear .positive case_56_50_17).check 56 50 17 = true := by
  change case_56_50_17.check 56 50 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_50_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_56_50_18_checked :
    (Witness.linear .positive case_56_50_18).check 56 50 18 = true := by
  change case_56_50_18.check 56 50 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_50_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_56_50_19_checked :
    (Witness.linear .positive case_56_50_19).check 56 50 19 = true := by
  change case_56_50_19.check 56 50 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_50_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900] }

theorem case_56_50_20_checked :
    (Witness.linear .positive case_56_50_20).check 56 50 20 = true := by
  change case_56_50_20.check 56 50 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_50_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440] }

theorem case_56_50_21_checked :
    (Witness.linear .positive case_56_50_21).check 56 50 21 = true := by
  change case_56_50_21.check 56 50 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_50_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670, 9694845] }

theorem case_56_50_22_checked :
    (Witness.linear .positive case_56_50_22).check 56 50 22 = true := by
  change case_56_50_22.check 56 50 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_50_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190, 477638700, 129644790, 35357670] }

theorem case_56_50_23_checked :
    (Witness.linear .positive case_56_50_23).check 56 50 23 = true := by
  change case_56_50_23.check 56 50 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_50_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020, 6564120420, 1767263190, 477638700, 129644790] }

theorem case_56_50_24_checked :
    (Witness.linear .positive case_56_50_24).check 56 50 24 = true := by
  change case_56_50_24.check 56 50 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_50_25 : Certificate := {
  objectiveScale := 1
  eta := 343059613650
  rows := #[]
  caps := #[0, 0, 91482563640, 24466267020, 6564120420, 1767263190, 477638700] }

theorem case_56_50_25_checked :
    (Witness.linear .positive case_56_50_25).check 56 50 25 = true := by
  change case_56_50_25.check 56 50 25 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_50_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 343059613650, 343059613650, 251577050010] }

theorem case_56_50_26_checked :
    (Witness.linear .negative case_56_50_26).check 56 50 26 = true := by
  change case_56_50_26.check 56 50 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_50_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 91482563640] }

theorem case_56_50_27_checked :
    (Witness.linear .negative case_56_50_27).check 56 50 27 = true := by
  change case_56_50_27.check 56 50 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_50_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_56_50_28_checked :
    (Witness.linear .negative case_56_50_28).check 56 50 28 = true := by
  change case_56_50_28.check 56 50 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_50_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_56_50_29_checked :
    (Witness.linear .negative case_56_50_29).check 56 50 29 = true := by
  change case_56_50_29.check 56 50 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_50_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_56_50_30_checked :
    (Witness.linear .negative case_56_50_30).check 56 50 30 = true := by
  change case_56_50_30.check 56 50 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_50_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_56_50_31_checked :
    (Witness.linear .negative case_56_50_31).check 56 50 31 = true := by
  change case_56_50_31.check 56 50 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_50_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_56_50_32_checked :
    (Witness.linear .negative case_56_50_32).check 56 50 32 = true := by
  change case_56_50_32.check 56 50 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_51_1_checked :
    (Witness.rising).check 56 51 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_51_2_checked :
    (Witness.rising).check 56 51 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_51_3_checked :
    (Witness.rising).check 56 51 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_51_4_checked :
    (Witness.rising).check 56 51 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_51_5_checked :
    (Witness.rising).check 56 51 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_51_6_checked :
    (Witness.rising).check 56 51 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_51_7_checked :
    (Witness.rising).check 56 51 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_51_8_checked :
    (Witness.rising).check 56 51 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_51_9_checked :
    (Witness.rising).check 56 51 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_51_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_56_51_10_checked :
    (Witness.linear .positive case_56_51_10).check 56 51 10 = true := by
  change case_56_51_10.check 56 51 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_51_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42] }

theorem case_56_51_11_checked :
    (Witness.linear .positive case_56_51_11).check 56 51 11 = true := by
  change case_56_51_11.check 56 51 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_51_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132] }

theorem case_56_51_12_checked :
    (Witness.linear .positive case_56_51_12).check 56 51 12 = true := by
  change case_56_51_12.check 56 51 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_51_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429] }

theorem case_56_51_13_checked :
    (Witness.linear .positive case_56_51_13).check 56 51 13 = true := by
  change case_56_51_13.check 56 51 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_51_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430] }

theorem case_56_51_14_checked :
    (Witness.linear .positive case_56_51_14).check 56 51 14 = true := by
  change case_56_51_14.check 56 51 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_51_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862] }

theorem case_56_51_15_checked :
    (Witness.linear .positive case_56_51_15).check 56 51 15 = true := by
  change case_56_51_15.check 56 51 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_51_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796] }

theorem case_56_51_16_checked :
    (Witness.linear .positive case_56_51_16).check 56 51 16 = true := by
  change case_56_51_16.check 56 51 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_51_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786] }

theorem case_56_51_17_checked :
    (Witness.linear .positive case_56_51_17).check 56 51 17 = true := by
  change case_56_51_17.check 56 51 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_51_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012] }

theorem case_56_51_18_checked :
    (Witness.linear .positive case_56_51_18).check 56 51 18 = true := by
  change case_56_51_18.check 56 51 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_51_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900] }

theorem case_56_51_19_checked :
    (Witness.linear .positive case_56_51_19).check 56 51 19 = true := by
  change case_56_51_19.check 56 51 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_51_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440] }

theorem case_56_51_20_checked :
    (Witness.linear .positive case_56_51_20).check 56 51 20 = true := by
  change case_56_51_20.check 56 51 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_51_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845] }

theorem case_56_51_21_checked :
    (Witness.linear .positive case_56_51_21).check 56 51 21 = true := by
  change case_56_51_21.check 56 51 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_51_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670] }

theorem case_56_51_22_checked :
    (Witness.linear .positive case_56_51_22).check 56 51 22 = true := by
  change case_56_51_22.check 56 51 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_51_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190, 477638700, 129644790] }

theorem case_56_51_23_checked :
    (Witness.linear .positive case_56_51_23).check 56 51 23 = true := by
  change case_56_51_23.check 56 51 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_51_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020, 6564120420, 1767263190, 477638700] }

theorem case_56_51_24_checked :
    (Witness.linear .positive case_56_51_24).check 56 51 24 = true := by
  change case_56_51_24.check 56 51 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_51_25 : Certificate := {
  objectiveScale := 1
  eta := 343059613650
  rows := #[]
  caps := #[0, 0, 91482563640, 24466267020, 6564120420, 1767263190] }

theorem case_56_51_25_checked :
    (Witness.linear .positive case_56_51_25).check 56 51 25 = true := by
  change case_56_51_25.check 56 51 25 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_51_26 : Certificate := {
  objectiveScale := 55
  eta := 17018415216
  rows := #[⟨.assumptionRow 26, 39⟩]
  caps := #[0, 0, 5507381880, 2086129500, 736281000, 241920900] }

theorem case_56_51_26_checked :
    (Witness.linear .conditional case_56_51_26).check 56 51 26 = true := by
  change case_56_51_26.check 56 51 26 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_51_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 343059613650] }

theorem case_56_51_27_checked :
    (Witness.linear .negative case_56_51_27).check 56 51 27 = true := by
  change case_56_51_27.check 56 51 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_51_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_56_51_28_checked :
    (Witness.linear .negative case_56_51_28).check 56 51 28 = true := by
  change case_56_51_28.check 56 51 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_51_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_56_51_29_checked :
    (Witness.linear .negative case_56_51_29).check 56 51 29 = true := by
  change case_56_51_29.check 56 51 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_51_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_56_51_30_checked :
    (Witness.linear .negative case_56_51_30).check 56 51 30 = true := by
  change case_56_51_30.check 56 51 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_51_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_56_51_31_checked :
    (Witness.linear .negative case_56_51_31).check 56 51 31 = true := by
  change case_56_51_31.check 56 51 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_51_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_56_51_32_checked :
    (Witness.linear .negative case_56_51_32).check 56 51 32 = true := by
  change case_56_51_32.check 56 51 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_51_33 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_56_51_33_checked :
    (Witness.linear .negative case_56_51_33).check 56 51 33 = true := by
  change case_56_51_33.check 56 51 33 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_52_1_checked :
    (Witness.rising).check 56 52 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_52_2_checked :
    (Witness.rising).check 56 52 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_52_3_checked :
    (Witness.rising).check 56 52 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_52_4_checked :
    (Witness.rising).check 56 52 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_52_5_checked :
    (Witness.rising).check 56 52 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_52_6_checked :
    (Witness.rising).check 56 52 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_52_7_checked :
    (Witness.rising).check 56 52 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_52_8_checked :
    (Witness.rising).check 56 52 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_52_9_checked :
    (Witness.rising).check 56 52 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_52_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_56_52_10_checked :
    (Witness.linear .positive case_56_52_10).check 56 52 10 = true := by
  change case_56_52_10.check 56 52 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_52_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_56_52_11_checked :
    (Witness.linear .positive case_56_52_11).check 56 52 11 = true := by
  change case_56_52_11.check 56 52 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_52_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429] }

theorem case_56_52_12_checked :
    (Witness.linear .positive case_56_52_12).check 56 52 12 = true := by
  change case_56_52_12.check 56 52 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_52_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430] }

theorem case_56_52_13_checked :
    (Witness.linear .positive case_56_52_13).check 56 52 13 = true := by
  change case_56_52_13.check 56 52 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_52_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862] }

theorem case_56_52_14_checked :
    (Witness.linear .positive case_56_52_14).check 56 52 14 = true := by
  change case_56_52_14.check 56 52 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_52_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796] }

theorem case_56_52_15_checked :
    (Witness.linear .positive case_56_52_15).check 56 52 15 = true := by
  change case_56_52_15.check 56 52 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_52_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786] }

theorem case_56_52_16_checked :
    (Witness.linear .positive case_56_52_16).check 56 52 16 = true := by
  change case_56_52_16.check 56 52 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_52_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012] }

theorem case_56_52_17_checked :
    (Witness.linear .positive case_56_52_17).check 56 52 17 = true := by
  change case_56_52_17.check 56 52 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_52_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900] }

theorem case_56_52_18_checked :
    (Witness.linear .positive case_56_52_18).check 56 52 18 = true := by
  change case_56_52_18.check 56 52 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_52_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440] }

theorem case_56_52_19_checked :
    (Witness.linear .positive case_56_52_19).check 56 52 19 = true := by
  change case_56_52_19.check 56 52 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_52_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845] }

theorem case_56_52_20_checked :
    (Witness.linear .positive case_56_52_20).check 56 52 20 = true := by
  change case_56_52_20.check 56 52 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_52_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670] }

theorem case_56_52_21_checked :
    (Witness.linear .positive case_56_52_21).check 56 52 21 = true := by
  change case_56_52_21.check 56 52 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_52_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790] }

theorem case_56_52_22_checked :
    (Witness.linear .positive case_56_52_22).check 56 52 22 = true := by
  change case_56_52_22.check 56 52 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_52_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190, 477638700] }

theorem case_56_52_23_checked :
    (Witness.linear .positive case_56_52_23).check 56 52 23 = true := by
  change case_56_52_23.check 56 52 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_52_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020, 6564120420, 1767263190] }

theorem case_56_52_24_checked :
    (Witness.linear .positive case_56_52_24).check 56 52 24 = true := by
  change case_56_52_24.check 56 52 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_52_25 : Certificate := {
  objectiveScale := 1
  eta := 343059613650
  rows := #[]
  caps := #[0, 0, 91482563640, 24466267020, 6564120420] }

theorem case_56_52_25_checked :
    (Witness.linear .positive case_56_52_25).check 56 52 25 = true := by
  change case_56_52_25.check 56 52 25 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_52_26 : Certificate := {
  objectiveScale := 1
  eta := 1289904147324
  rows := #[]
  caps := #[0, 0, 343059613650, 91482563640, 24466267020] }

theorem case_56_52_26_checked :
    (Witness.linear .positive case_56_52_26).check 56 52 26 = true := by
  change case_56_52_26.check 56 52 26 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_52_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 1289904147324] }

theorem case_56_52_27_checked :
    (Witness.linear .negative case_56_52_27).check 56 52 27 = true := by
  change case_56_52_27.check 56 52 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_52_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_56_52_28_checked :
    (Witness.linear .negative case_56_52_28).check 56 52 28 = true := by
  change case_56_52_28.check 56 52 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_52_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_56_52_29_checked :
    (Witness.linear .negative case_56_52_29).check 56 52 29 = true := by
  change case_56_52_29.check 56 52 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_52_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_56_52_30_checked :
    (Witness.linear .negative case_56_52_30).check 56 52 30 = true := by
  change case_56_52_30.check 56 52 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_52_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_56_52_31_checked :
    (Witness.linear .negative case_56_52_31).check 56 52 31 = true := by
  change case_56_52_31.check 56 52 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_52_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_56_52_32_checked :
    (Witness.linear .negative case_56_52_32).check 56 52 32 = true := by
  change case_56_52_32.check 56 52 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_52_33 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_56_52_33_checked :
    (Witness.linear .negative case_56_52_33).check 56 52 33 = true := by
  change case_56_52_33.check 56 52 33 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_52_34 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_56_52_34_checked :
    (Witness.linear .negative case_56_52_34).check 56 52 34 = true := by
  change case_56_52_34.check 56 52 34 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_53_1_checked :
    (Witness.rising).check 56 53 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_53_2_checked :
    (Witness.rising).check 56 53 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_53_3_checked :
    (Witness.rising).check 56 53 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_53_4_checked :
    (Witness.rising).check 56 53 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_53_5_checked :
    (Witness.rising).check 56 53 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_53_6_checked :
    (Witness.rising).check 56 53 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_53_7_checked :
    (Witness.rising).check 56 53 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_53_8_checked :
    (Witness.rising).check 56 53 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_53_9_checked :
    (Witness.rising).check 56 53 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_53_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_56_53_10_checked :
    (Witness.linear .positive case_56_53_10).check 56 53 10 = true := by
  change case_56_53_10.check 56 53 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_53_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_56_53_11_checked :
    (Witness.linear .positive case_56_53_11).check 56 53 11 = true := by
  change case_56_53_11.check 56 53 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_53_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430] }

theorem case_56_53_12_checked :
    (Witness.linear .positive case_56_53_12).check 56 53 12 = true := by
  change case_56_53_12.check 56 53 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_53_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862] }

theorem case_56_53_13_checked :
    (Witness.linear .positive case_56_53_13).check 56 53 13 = true := by
  change case_56_53_13.check 56 53 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_53_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796] }

theorem case_56_53_14_checked :
    (Witness.linear .positive case_56_53_14).check 56 53 14 = true := by
  change case_56_53_14.check 56 53 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_53_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786] }

theorem case_56_53_15_checked :
    (Witness.linear .positive case_56_53_15).check 56 53 15 = true := by
  change case_56_53_15.check 56 53 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_53_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012] }

theorem case_56_53_16_checked :
    (Witness.linear .positive case_56_53_16).check 56 53 16 = true := by
  change case_56_53_16.check 56 53 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_53_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900] }

theorem case_56_53_17_checked :
    (Witness.linear .positive case_56_53_17).check 56 53 17 = true := by
  change case_56_53_17.check 56 53 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_53_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440] }

theorem case_56_53_18_checked :
    (Witness.linear .positive case_56_53_18).check 56 53 18 = true := by
  change case_56_53_18.check 56 53 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_53_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845] }

theorem case_56_53_19_checked :
    (Witness.linear .positive case_56_53_19).check 56 53 19 = true := by
  change case_56_53_19.check 56 53 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_53_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670] }

theorem case_56_53_20_checked :
    (Witness.linear .positive case_56_53_20).check 56 53 20 = true := by
  change case_56_53_20.check 56 53 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_53_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790] }

theorem case_56_53_21_checked :
    (Witness.linear .positive case_56_53_21).check 56 53 21 = true := by
  change case_56_53_21.check 56 53 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_53_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700] }

theorem case_56_53_22_checked :
    (Witness.linear .positive case_56_53_22).check 56 53 22 = true := by
  change case_56_53_22.check 56 53 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_53_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190] }

theorem case_56_53_23_checked :
    (Witness.linear .positive case_56_53_23).check 56 53 23 = true := by
  change case_56_53_23.check 56 53 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_53_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020, 6564120420] }

theorem case_56_53_24_checked :
    (Witness.linear .positive case_56_53_24).check 56 53 24 = true := by
  change case_56_53_24.check 56 53 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_53_25 : Certificate := {
  objectiveScale := 1
  eta := 343059613650
  rows := #[]
  caps := #[0, 0, 91482563640, 24466267020] }

theorem case_56_53_25_checked :
    (Witness.linear .positive case_56_53_25).check 56 53 25 = true := by
  change case_56_53_25.check 56 53 25 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_53_26 : Certificate := {
  objectiveScale := 1
  eta := 1289904147324
  rows := #[]
  caps := #[0, 0, 343059613650, 91482563640] }

theorem case_56_53_26_checked :
    (Witness.linear .positive case_56_53_26).check 56 53 26 = true := by
  change case_56_53_26.check 56 53 26 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_53_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 4861946401452] }

theorem case_56_53_27_checked :
    (Witness.linear .negative case_56_53_27).check 56 53 27 = true := by
  change case_56_53_27.check 56 53 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_53_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_56_53_28_checked :
    (Witness.linear .negative case_56_53_28).check 56 53 28 = true := by
  change case_56_53_28.check 56 53 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_53_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_56_53_29_checked :
    (Witness.linear .negative case_56_53_29).check 56 53 29 = true := by
  change case_56_53_29.check 56 53 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_53_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_56_53_30_checked :
    (Witness.linear .negative case_56_53_30).check 56 53 30 = true := by
  change case_56_53_30.check 56 53 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_53_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_56_53_31_checked :
    (Witness.linear .negative case_56_53_31).check 56 53 31 = true := by
  change case_56_53_31.check 56 53 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_53_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_56_53_32_checked :
    (Witness.linear .negative case_56_53_32).check 56 53 32 = true := by
  change case_56_53_32.check 56 53 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_53_33 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_56_53_33_checked :
    (Witness.linear .negative case_56_53_33).check 56 53 33 = true := by
  change case_56_53_33.check 56 53 33 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_53_34 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_56_53_34_checked :
    (Witness.linear .negative case_56_53_34).check 56 53 34 = true := by
  change case_56_53_34.check 56 53 34 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_54_1_checked :
    (Witness.rising).check 56 54 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_54_2_checked :
    (Witness.rising).check 56 54 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_54_3_checked :
    (Witness.rising).check 56 54 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_54_4_checked :
    (Witness.rising).check 56 54 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_54_5_checked :
    (Witness.rising).check 56 54 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_54_6_checked :
    (Witness.rising).check 56 54 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_54_7_checked :
    (Witness.rising).check 56 54 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_54_8_checked :
    (Witness.rising).check 56 54 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_54_9_checked :
    (Witness.rising).check 56 54 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_54_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_56_54_10_checked :
    (Witness.linear .positive case_56_54_10).check 56 54 10 = true := by
  change case_56_54_10.check 56 54 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_54_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_56_54_11_checked :
    (Witness.linear .positive case_56_54_11).check 56 54 11 = true := by
  change case_56_54_11.check 56 54 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_54_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_56_54_12_checked :
    (Witness.linear .positive case_56_54_12).check 56 54 12 = true := by
  change case_56_54_12.check 56 54 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_54_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796] }

theorem case_56_54_13_checked :
    (Witness.linear .positive case_56_54_13).check 56 54 13 = true := by
  change case_56_54_13.check 56 54 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_54_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786] }

theorem case_56_54_14_checked :
    (Witness.linear .positive case_56_54_14).check 56 54 14 = true := by
  change case_56_54_14.check 56 54 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_54_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012] }

theorem case_56_54_15_checked :
    (Witness.linear .positive case_56_54_15).check 56 54 15 = true := by
  change case_56_54_15.check 56 54 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_54_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900] }

theorem case_56_54_16_checked :
    (Witness.linear .positive case_56_54_16).check 56 54 16 = true := by
  change case_56_54_16.check 56 54 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_54_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440] }

theorem case_56_54_17_checked :
    (Witness.linear .positive case_56_54_17).check 56 54 17 = true := by
  change case_56_54_17.check 56 54 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_54_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845] }

theorem case_56_54_18_checked :
    (Witness.linear .positive case_56_54_18).check 56 54 18 = true := by
  change case_56_54_18.check 56 54 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_54_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670] }

theorem case_56_54_19_checked :
    (Witness.linear .positive case_56_54_19).check 56 54 19 = true := by
  change case_56_54_19.check 56 54 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_54_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790] }

theorem case_56_54_20_checked :
    (Witness.linear .positive case_56_54_20).check 56 54 20 = true := by
  change case_56_54_20.check 56 54 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_54_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700] }

theorem case_56_54_21_checked :
    (Witness.linear .positive case_56_54_21).check 56 54 21 = true := by
  change case_56_54_21.check 56 54 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_54_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190] }

theorem case_56_54_22_checked :
    (Witness.linear .positive case_56_54_22).check 56 54 22 = true := by
  change case_56_54_22.check 56 54 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_54_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420] }

theorem case_56_54_23_checked :
    (Witness.linear .positive case_56_54_23).check 56 54 23 = true := by
  change case_56_54_23.check 56 54 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_54_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020] }

theorem case_56_54_24_checked :
    (Witness.linear .positive case_56_54_24).check 56 54 24 = true := by
  change case_56_54_24.check 56 54 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_54_25 : Certificate := {
  objectiveScale := 1
  eta := 343059613650
  rows := #[]
  caps := #[0, 0, 91482563640] }

theorem case_56_54_25_checked :
    (Witness.linear .positive case_56_54_25).check 56 54 25 = true := by
  change case_56_54_25.check 56 54 25 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_54_26 : Certificate := {
  objectiveScale := 1
  eta := 1289904147324
  rows := #[]
  caps := #[0, 0, 343059613650] }

theorem case_56_54_26_checked :
    (Witness.linear .positive case_56_54_26).check 56 54 26 = true := by
  change case_56_54_26.check 56 54 26 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_54_27 : Certificate := {
  objectiveScale := 1
  eta := 4861946401452
  rows := #[]
  caps := #[0, 0, 1289904147324] }

theorem case_56_54_27_checked :
    (Witness.linear .positive case_56_54_27).check 56 54 27 = true := by
  change case_56_54_27.check 56 54 27 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_54_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_56_54_28_checked :
    (Witness.linear .negative case_56_54_28).check 56 54 28 = true := by
  change case_56_54_28.check 56 54 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_54_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_56_54_29_checked :
    (Witness.linear .negative case_56_54_29).check 56 54 29 = true := by
  change case_56_54_29.check 56 54 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_54_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_56_54_30_checked :
    (Witness.linear .negative case_56_54_30).check 56 54 30 = true := by
  change case_56_54_30.check 56 54 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_54_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_56_54_31_checked :
    (Witness.linear .negative case_56_54_31).check 56 54 31 = true := by
  change case_56_54_31.check 56 54 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_54_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_56_54_32_checked :
    (Witness.linear .negative case_56_54_32).check 56 54 32 = true := by
  change case_56_54_32.check 56 54 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_54_33 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_56_54_33_checked :
    (Witness.linear .negative case_56_54_33).check 56 54 33 = true := by
  change case_56_54_33.check 56 54 33 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_54_34 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_56_54_34_checked :
    (Witness.linear .negative case_56_54_34).check 56 54 34 = true := by
  change case_56_54_34.check 56 54 34 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_54_35 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_56_54_35_checked :
    (Witness.linear .negative case_56_54_35).check 56 54 35 = true := by
  change case_56_54_35.check 56 54 35 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_55_1_checked :
    (Witness.rising).check 56 55 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_55_2_checked :
    (Witness.rising).check 56 55 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_55_3_checked :
    (Witness.rising).check 56 55 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_55_4_checked :
    (Witness.rising).check 56 55 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_55_5_checked :
    (Witness.rising).check 56 55 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_55_6_checked :
    (Witness.rising).check 56 55 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_55_7_checked :
    (Witness.rising).check 56 55 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_55_8_checked :
    (Witness.rising).check 56 55 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_56_55_9_checked :
    (Witness.rising).check 56 55 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_55_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_56_55_10_checked :
    (Witness.linear .positive case_56_55_10).check 56 55 10 = true := by
  change case_56_55_10.check 56 55 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_55_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_56_55_11_checked :
    (Witness.linear .positive case_56_55_11).check 56 55 11 = true := by
  change case_56_55_11.check 56 55 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_55_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_56_55_12_checked :
    (Witness.linear .positive case_56_55_12).check 56 55 12 = true := by
  change case_56_55_12.check 56 55 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_55_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0] }

theorem case_56_55_13_checked :
    (Witness.linear .positive case_56_55_13).check 56 55 13 = true := by
  change case_56_55_13.check 56 55 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_55_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0] }

theorem case_56_55_14_checked :
    (Witness.linear .positive case_56_55_14).check 56 55 14 = true := by
  change case_56_55_14.check 56 55 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_55_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0] }

theorem case_56_55_15_checked :
    (Witness.linear .positive case_56_55_15).check 56 55 15 = true := by
  change case_56_55_15.check 56 55 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_55_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0] }

theorem case_56_55_16_checked :
    (Witness.linear .positive case_56_55_16).check 56 55 16 = true := by
  change case_56_55_16.check 56 55 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_55_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0] }

theorem case_56_55_17_checked :
    (Witness.linear .positive case_56_55_17).check 56 55 17 = true := by
  change case_56_55_17.check 56 55 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_55_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0] }

theorem case_56_55_18_checked :
    (Witness.linear .positive case_56_55_18).check 56 55 18 = true := by
  change case_56_55_18.check 56 55 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_55_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0] }

theorem case_56_55_19_checked :
    (Witness.linear .positive case_56_55_19).check 56 55 19 = true := by
  change case_56_55_19.check 56 55 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_55_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0] }

theorem case_56_55_20_checked :
    (Witness.linear .positive case_56_55_20).check 56 55 20 = true := by
  change case_56_55_20.check 56 55 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_55_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0] }

theorem case_56_55_21_checked :
    (Witness.linear .positive case_56_55_21).check 56 55 21 = true := by
  change case_56_55_21.check 56 55 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_55_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0] }

theorem case_56_55_22_checked :
    (Witness.linear .positive case_56_55_22).check 56 55 22 = true := by
  change case_56_55_22.check 56 55 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_55_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0] }

theorem case_56_55_23_checked :
    (Witness.linear .positive case_56_55_23).check 56 55 23 = true := by
  change case_56_55_23.check 56 55 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_55_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0] }

theorem case_56_55_24_checked :
    (Witness.linear .positive case_56_55_24).check 56 55 24 = true := by
  change case_56_55_24.check 56 55 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_55_25 : Certificate := {
  objectiveScale := 1
  eta := 343059613650
  rows := #[]
  caps := #[0, 0] }

theorem case_56_55_25_checked :
    (Witness.linear .positive case_56_55_25).check 56 55 25 = true := by
  change case_56_55_25.check 56 55 25 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_55_26 : Certificate := {
  objectiveScale := 1
  eta := 1289904147324
  rows := #[]
  caps := #[0, 0] }

theorem case_56_55_26_checked :
    (Witness.linear .positive case_56_55_26).check 56 55 26 = true := by
  change case_56_55_26.check 56 55 26 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_55_27 : Certificate := {
  objectiveScale := 1
  eta := 4861946401452
  rows := #[]
  caps := #[0, 0] }

theorem case_56_55_27_checked :
    (Witness.linear .positive case_56_55_27).check 56 55 27 = true := by
  change case_56_55_27.check 56 55 27 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_55_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_56_55_28_checked :
    (Witness.linear .negative case_56_55_28).check 56 55 28 = true := by
  change case_56_55_28.check 56 55 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_55_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_56_55_29_checked :
    (Witness.linear .negative case_56_55_29).check 56 55 29 = true := by
  change case_56_55_29.check 56 55 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_55_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_56_55_30_checked :
    (Witness.linear .negative case_56_55_30).check 56 55 30 = true := by
  change case_56_55_30.check 56 55 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_55_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_56_55_31_checked :
    (Witness.linear .negative case_56_55_31).check 56 55 31 = true := by
  change case_56_55_31.check 56 55 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_55_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_56_55_32_checked :
    (Witness.linear .negative case_56_55_32).check 56 55 32 = true := by
  change case_56_55_32.check 56 55 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_55_33 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_56_55_33_checked :
    (Witness.linear .negative case_56_55_33).check 56 55 33 = true := by
  change case_56_55_33.check 56 55 33 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_55_34 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_56_55_34_checked :
    (Witness.linear .negative case_56_55_34).check 56 55 34 = true := by
  change case_56_55_34.check 56 55 34 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_55_35 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_56_55_35_checked :
    (Witness.linear .negative case_56_55_35).check 56 55 35 = true := by
  change case_56_55_35.check 56 55 35 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_56_55_36 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_56_55_36_checked :
    (Witness.linear .negative case_56_55_36).check 56 55 36 = true := by
  change case_56_55_36.check 56 55 36 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_56 (a k : ℕ) (h : Domain 56 a k) :
    ∃ w : Witness, w.check 56 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 28 ≤ a := by omega
  have haHi : a ≤ 55 := by omega
  interval_cases a

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_56_28_1_checked⟩

    · exact ⟨Witness.rising, case_56_28_2_checked⟩

    · exact ⟨Witness.rising, case_56_28_3_checked⟩

    · exact ⟨Witness.rising, case_56_28_4_checked⟩

    · exact ⟨Witness.rising, case_56_28_5_checked⟩

    · exact ⟨Witness.rising, case_56_28_6_checked⟩

    · exact ⟨Witness.rising, case_56_28_7_checked⟩

    · exact ⟨Witness.rising, case_56_28_8_checked⟩

    · exact ⟨Witness.rising, case_56_28_9_checked⟩

    · exact ⟨Witness.rising, case_56_28_10_checked⟩

    · exact ⟨Witness.linear .positive case_56_28_11, case_56_28_11_checked⟩

    · exact ⟨Witness.linear .positive case_56_28_12, case_56_28_12_checked⟩

    · exact ⟨Witness.linear .positive case_56_28_13, case_56_28_13_checked⟩

    · exact ⟨Witness.linear .positive case_56_28_14, case_56_28_14_checked⟩

    · exact ⟨Witness.linear .positive case_56_28_15, case_56_28_15_checked⟩

    · exact ⟨Witness.linear .conditional case_56_28_16, case_56_28_16_checked⟩

    · exact ⟨Witness.linear .conditional case_56_28_17, case_56_28_17_checked⟩

    · exact ⟨Witness.linear .conditional case_56_28_18, case_56_28_18_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_56_29_1_checked⟩

    · exact ⟨Witness.rising, case_56_29_2_checked⟩

    · exact ⟨Witness.rising, case_56_29_3_checked⟩

    · exact ⟨Witness.rising, case_56_29_4_checked⟩

    · exact ⟨Witness.rising, case_56_29_5_checked⟩

    · exact ⟨Witness.rising, case_56_29_6_checked⟩

    · exact ⟨Witness.rising, case_56_29_7_checked⟩

    · exact ⟨Witness.rising, case_56_29_8_checked⟩

    · exact ⟨Witness.rising, case_56_29_9_checked⟩

    · exact ⟨Witness.rising, case_56_29_10_checked⟩

    · exact ⟨Witness.linear .positive case_56_29_11, case_56_29_11_checked⟩

    · exact ⟨Witness.linear .positive case_56_29_12, case_56_29_12_checked⟩

    · exact ⟨Witness.linear .positive case_56_29_13, case_56_29_13_checked⟩

    · exact ⟨Witness.linear .positive case_56_29_14, case_56_29_14_checked⟩

    · exact ⟨Witness.linear .positive case_56_29_15, case_56_29_15_checked⟩

    · exact ⟨Witness.linear .conditional case_56_29_16, case_56_29_16_checked⟩

    · exact ⟨Witness.linear .conditional case_56_29_17, case_56_29_17_checked⟩

    · exact ⟨Witness.linear .conditional case_56_29_18, case_56_29_18_checked⟩

  · have hkHi : k ≤ 19 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_56_30_1_checked⟩

    · exact ⟨Witness.rising, case_56_30_2_checked⟩

    · exact ⟨Witness.rising, case_56_30_3_checked⟩

    · exact ⟨Witness.rising, case_56_30_4_checked⟩

    · exact ⟨Witness.rising, case_56_30_5_checked⟩

    · exact ⟨Witness.rising, case_56_30_6_checked⟩

    · exact ⟨Witness.rising, case_56_30_7_checked⟩

    · exact ⟨Witness.rising, case_56_30_8_checked⟩

    · exact ⟨Witness.rising, case_56_30_9_checked⟩

    · exact ⟨Witness.rising, case_56_30_10_checked⟩

    · exact ⟨Witness.linear .positive case_56_30_11, case_56_30_11_checked⟩

    · exact ⟨Witness.linear .positive case_56_30_12, case_56_30_12_checked⟩

    · exact ⟨Witness.linear .positive case_56_30_13, case_56_30_13_checked⟩

    · exact ⟨Witness.linear .positive case_56_30_14, case_56_30_14_checked⟩

    · exact ⟨Witness.linear .positive case_56_30_15, case_56_30_15_checked⟩

    · exact ⟨Witness.linear .conditional case_56_30_16, case_56_30_16_checked⟩

    · exact ⟨Witness.linear .conditional case_56_30_17, case_56_30_17_checked⟩

    · exact ⟨Witness.linear .conditional case_56_30_18, case_56_30_18_checked⟩

    · exact ⟨Witness.linear .conditional case_56_30_19, case_56_30_19_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_56_31_1_checked⟩

    · exact ⟨Witness.rising, case_56_31_2_checked⟩

    · exact ⟨Witness.rising, case_56_31_3_checked⟩

    · exact ⟨Witness.rising, case_56_31_4_checked⟩

    · exact ⟨Witness.rising, case_56_31_5_checked⟩

    · exact ⟨Witness.rising, case_56_31_6_checked⟩

    · exact ⟨Witness.rising, case_56_31_7_checked⟩

    · exact ⟨Witness.rising, case_56_31_8_checked⟩

    · exact ⟨Witness.rising, case_56_31_9_checked⟩

    · exact ⟨Witness.rising, case_56_31_10_checked⟩

    · exact ⟨Witness.linear .positive case_56_31_11, case_56_31_11_checked⟩

    · exact ⟨Witness.linear .positive case_56_31_12, case_56_31_12_checked⟩

    · exact ⟨Witness.linear .positive case_56_31_13, case_56_31_13_checked⟩

    · exact ⟨Witness.linear .positive case_56_31_14, case_56_31_14_checked⟩

    · exact ⟨Witness.linear .positive case_56_31_15, case_56_31_15_checked⟩

    · exact ⟨Witness.linear .positive case_56_31_16, case_56_31_16_checked⟩

    · exact ⟨Witness.linear .conditional case_56_31_17, case_56_31_17_checked⟩

    · exact ⟨Witness.linear .conditional case_56_31_18, case_56_31_18_checked⟩

    · exact ⟨Witness.linear .conditional case_56_31_19, case_56_31_19_checked⟩

    · exact ⟨Witness.linear .conditional case_56_31_20, case_56_31_20_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_56_32_1_checked⟩

    · exact ⟨Witness.rising, case_56_32_2_checked⟩

    · exact ⟨Witness.rising, case_56_32_3_checked⟩

    · exact ⟨Witness.rising, case_56_32_4_checked⟩

    · exact ⟨Witness.rising, case_56_32_5_checked⟩

    · exact ⟨Witness.rising, case_56_32_6_checked⟩

    · exact ⟨Witness.rising, case_56_32_7_checked⟩

    · exact ⟨Witness.rising, case_56_32_8_checked⟩

    · exact ⟨Witness.rising, case_56_32_9_checked⟩

    · exact ⟨Witness.rising, case_56_32_10_checked⟩

    · exact ⟨Witness.linear .positive case_56_32_11, case_56_32_11_checked⟩

    · exact ⟨Witness.linear .positive case_56_32_12, case_56_32_12_checked⟩

    · exact ⟨Witness.linear .positive case_56_32_13, case_56_32_13_checked⟩

    · exact ⟨Witness.linear .positive case_56_32_14, case_56_32_14_checked⟩

    · exact ⟨Witness.linear .positive case_56_32_15, case_56_32_15_checked⟩

    · exact ⟨Witness.linear .positive case_56_32_16, case_56_32_16_checked⟩

    · exact ⟨Witness.linear .conditional case_56_32_17, case_56_32_17_checked⟩

    · exact ⟨Witness.linear .conditional case_56_32_18, case_56_32_18_checked⟩

    · exact ⟨Witness.linear .conditional case_56_32_19, case_56_32_19_checked⟩

    · exact ⟨Witness.linear .conditional case_56_32_20, case_56_32_20_checked⟩

  · have hkHi : k ≤ 21 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_56_33_1_checked⟩

    · exact ⟨Witness.rising, case_56_33_2_checked⟩

    · exact ⟨Witness.rising, case_56_33_3_checked⟩

    · exact ⟨Witness.rising, case_56_33_4_checked⟩

    · exact ⟨Witness.rising, case_56_33_5_checked⟩

    · exact ⟨Witness.rising, case_56_33_6_checked⟩

    · exact ⟨Witness.rising, case_56_33_7_checked⟩

    · exact ⟨Witness.rising, case_56_33_8_checked⟩

    · exact ⟨Witness.rising, case_56_33_9_checked⟩

    · exact ⟨Witness.rising, case_56_33_10_checked⟩

    · exact ⟨Witness.linear .positive case_56_33_11, case_56_33_11_checked⟩

    · exact ⟨Witness.linear .positive case_56_33_12, case_56_33_12_checked⟩

    · exact ⟨Witness.linear .positive case_56_33_13, case_56_33_13_checked⟩

    · exact ⟨Witness.linear .positive case_56_33_14, case_56_33_14_checked⟩

    · exact ⟨Witness.linear .positive case_56_33_15, case_56_33_15_checked⟩

    · exact ⟨Witness.linear .positive case_56_33_16, case_56_33_16_checked⟩

    · exact ⟨Witness.linear .conditional case_56_33_17, case_56_33_17_checked⟩

    · exact ⟨Witness.linear .conditional case_56_33_18, case_56_33_18_checked⟩

    · exact ⟨Witness.linear .conditional case_56_33_19, case_56_33_19_checked⟩

    · exact ⟨Witness.linear .conditional case_56_33_20, case_56_33_20_checked⟩

    · exact ⟨Witness.linear .conditional case_56_33_21, case_56_33_21_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_56_34_1_checked⟩

    · exact ⟨Witness.rising, case_56_34_2_checked⟩

    · exact ⟨Witness.rising, case_56_34_3_checked⟩

    · exact ⟨Witness.rising, case_56_34_4_checked⟩

    · exact ⟨Witness.rising, case_56_34_5_checked⟩

    · exact ⟨Witness.rising, case_56_34_6_checked⟩

    · exact ⟨Witness.rising, case_56_34_7_checked⟩

    · exact ⟨Witness.rising, case_56_34_8_checked⟩

    · exact ⟨Witness.rising, case_56_34_9_checked⟩

    · exact ⟨Witness.rising, case_56_34_10_checked⟩

    · exact ⟨Witness.linear .positive case_56_34_11, case_56_34_11_checked⟩

    · exact ⟨Witness.linear .positive case_56_34_12, case_56_34_12_checked⟩

    · exact ⟨Witness.linear .positive case_56_34_13, case_56_34_13_checked⟩

    · exact ⟨Witness.linear .positive case_56_34_14, case_56_34_14_checked⟩

    · exact ⟨Witness.linear .positive case_56_34_15, case_56_34_15_checked⟩

    · exact ⟨Witness.linear .positive case_56_34_16, case_56_34_16_checked⟩

    · exact ⟨Witness.linear .conditional case_56_34_17, case_56_34_17_checked⟩

    · exact ⟨Witness.linear .conditional case_56_34_18, case_56_34_18_checked⟩

    · exact ⟨Witness.linear .conditional case_56_34_19, case_56_34_19_checked⟩

    · exact ⟨Witness.linear .conditional case_56_34_20, case_56_34_20_checked⟩

    · exact ⟨Witness.linear .conditional case_56_34_21, case_56_34_21_checked⟩

    · exact ⟨Witness.linear .conditional case_56_34_22, case_56_34_22_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_56_35_1_checked⟩

    · exact ⟨Witness.rising, case_56_35_2_checked⟩

    · exact ⟨Witness.rising, case_56_35_3_checked⟩

    · exact ⟨Witness.rising, case_56_35_4_checked⟩

    · exact ⟨Witness.rising, case_56_35_5_checked⟩

    · exact ⟨Witness.rising, case_56_35_6_checked⟩

    · exact ⟨Witness.rising, case_56_35_7_checked⟩

    · exact ⟨Witness.rising, case_56_35_8_checked⟩

    · exact ⟨Witness.rising, case_56_35_9_checked⟩

    · exact ⟨Witness.rising, case_56_35_10_checked⟩

    · exact ⟨Witness.linear .positive case_56_35_11, case_56_35_11_checked⟩

    · exact ⟨Witness.linear .positive case_56_35_12, case_56_35_12_checked⟩

    · exact ⟨Witness.linear .positive case_56_35_13, case_56_35_13_checked⟩

    · exact ⟨Witness.linear .positive case_56_35_14, case_56_35_14_checked⟩

    · exact ⟨Witness.linear .positive case_56_35_15, case_56_35_15_checked⟩

    · exact ⟨Witness.linear .positive case_56_35_16, case_56_35_16_checked⟩

    · exact ⟨Witness.linear .positive case_56_35_17, case_56_35_17_checked⟩

    · exact ⟨Witness.linear .conditional case_56_35_18, case_56_35_18_checked⟩

    · exact ⟨Witness.linear .conditional case_56_35_19, case_56_35_19_checked⟩

    · exact ⟨Witness.linear .conditional case_56_35_20, case_56_35_20_checked⟩

    · exact ⟨Witness.linear .conditional case_56_35_21, case_56_35_21_checked⟩

    · exact ⟨Witness.linear .conditional case_56_35_22, case_56_35_22_checked⟩

  · have hkHi : k ≤ 23 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_56_36_1_checked⟩

    · exact ⟨Witness.rising, case_56_36_2_checked⟩

    · exact ⟨Witness.rising, case_56_36_3_checked⟩

    · exact ⟨Witness.rising, case_56_36_4_checked⟩

    · exact ⟨Witness.rising, case_56_36_5_checked⟩

    · exact ⟨Witness.rising, case_56_36_6_checked⟩

    · exact ⟨Witness.rising, case_56_36_7_checked⟩

    · exact ⟨Witness.rising, case_56_36_8_checked⟩

    · exact ⟨Witness.rising, case_56_36_9_checked⟩

    · exact ⟨Witness.rising, case_56_36_10_checked⟩

    · exact ⟨Witness.linear .positive case_56_36_11, case_56_36_11_checked⟩

    · exact ⟨Witness.linear .positive case_56_36_12, case_56_36_12_checked⟩

    · exact ⟨Witness.linear .positive case_56_36_13, case_56_36_13_checked⟩

    · exact ⟨Witness.linear .positive case_56_36_14, case_56_36_14_checked⟩

    · exact ⟨Witness.linear .positive case_56_36_15, case_56_36_15_checked⟩

    · exact ⟨Witness.linear .positive case_56_36_16, case_56_36_16_checked⟩

    · exact ⟨Witness.linear .positive case_56_36_17, case_56_36_17_checked⟩

    · exact ⟨Witness.linear .conditional case_56_36_18, case_56_36_18_checked⟩

    · exact ⟨Witness.linear .conditional case_56_36_19, case_56_36_19_checked⟩

    · exact ⟨Witness.linear .conditional case_56_36_20, case_56_36_20_checked⟩

    · exact ⟨Witness.linear .conditional case_56_36_21, case_56_36_21_checked⟩

    · exact ⟨Witness.linear .conditional case_56_36_22, case_56_36_22_checked⟩

    · exact ⟨Witness.linear .conditional case_56_36_23, case_56_36_23_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_56_37_1_checked⟩

    · exact ⟨Witness.rising, case_56_37_2_checked⟩

    · exact ⟨Witness.rising, case_56_37_3_checked⟩

    · exact ⟨Witness.rising, case_56_37_4_checked⟩

    · exact ⟨Witness.rising, case_56_37_5_checked⟩

    · exact ⟨Witness.rising, case_56_37_6_checked⟩

    · exact ⟨Witness.rising, case_56_37_7_checked⟩

    · exact ⟨Witness.rising, case_56_37_8_checked⟩

    · exact ⟨Witness.rising, case_56_37_9_checked⟩

    · exact ⟨Witness.rising, case_56_37_10_checked⟩

    · exact ⟨Witness.linear .positive case_56_37_11, case_56_37_11_checked⟩

    · exact ⟨Witness.linear .positive case_56_37_12, case_56_37_12_checked⟩

    · exact ⟨Witness.linear .positive case_56_37_13, case_56_37_13_checked⟩

    · exact ⟨Witness.linear .positive case_56_37_14, case_56_37_14_checked⟩

    · exact ⟨Witness.linear .positive case_56_37_15, case_56_37_15_checked⟩

    · exact ⟨Witness.linear .positive case_56_37_16, case_56_37_16_checked⟩

    · exact ⟨Witness.linear .conditional case_56_37_17, case_56_37_17_checked⟩

    · exact ⟨Witness.linear .conditional case_56_37_18, case_56_37_18_checked⟩

    · exact ⟨Witness.linear .conditional case_56_37_19, case_56_37_19_checked⟩

    · exact ⟨Witness.linear .conditional case_56_37_20, case_56_37_20_checked⟩

    · exact ⟨Witness.linear .conditional case_56_37_21, case_56_37_21_checked⟩

    · exact ⟨Witness.linear .conditional case_56_37_22, case_56_37_22_checked⟩

    · exact ⟨Witness.linear .conditional case_56_37_23, case_56_37_23_checked⟩

    · exact ⟨Witness.linear .conditional case_56_37_24, case_56_37_24_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_56_38_1_checked⟩

    · exact ⟨Witness.rising, case_56_38_2_checked⟩

    · exact ⟨Witness.rising, case_56_38_3_checked⟩

    · exact ⟨Witness.rising, case_56_38_4_checked⟩

    · exact ⟨Witness.rising, case_56_38_5_checked⟩

    · exact ⟨Witness.rising, case_56_38_6_checked⟩

    · exact ⟨Witness.rising, case_56_38_7_checked⟩

    · exact ⟨Witness.rising, case_56_38_8_checked⟩

    · exact ⟨Witness.rising, case_56_38_9_checked⟩

    · exact ⟨Witness.rising, case_56_38_10_checked⟩

    · exact ⟨Witness.linear .positive case_56_38_11, case_56_38_11_checked⟩

    · exact ⟨Witness.linear .positive case_56_38_12, case_56_38_12_checked⟩

    · exact ⟨Witness.linear .positive case_56_38_13, case_56_38_13_checked⟩

    · exact ⟨Witness.linear .positive case_56_38_14, case_56_38_14_checked⟩

    · exact ⟨Witness.linear .positive case_56_38_15, case_56_38_15_checked⟩

    · exact ⟨Witness.linear .positive case_56_38_16, case_56_38_16_checked⟩

    · exact ⟨Witness.linear .positive case_56_38_17, case_56_38_17_checked⟩

    · exact ⟨Witness.linear .conditional case_56_38_18, case_56_38_18_checked⟩

    · exact ⟨Witness.linear .conditional case_56_38_19, case_56_38_19_checked⟩

    · exact ⟨Witness.linear .conditional case_56_38_20, case_56_38_20_checked⟩

    · exact ⟨Witness.linear .conditional case_56_38_21, case_56_38_21_checked⟩

    · exact ⟨Witness.linear .conditional case_56_38_22, case_56_38_22_checked⟩

    · exact ⟨Witness.linear .conditional case_56_38_23, case_56_38_23_checked⟩

    · exact ⟨Witness.linear .conditional case_56_38_24, case_56_38_24_checked⟩

  · have hkHi : k ≤ 25 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_56_39_1_checked⟩

    · exact ⟨Witness.rising, case_56_39_2_checked⟩

    · exact ⟨Witness.rising, case_56_39_3_checked⟩

    · exact ⟨Witness.rising, case_56_39_4_checked⟩

    · exact ⟨Witness.rising, case_56_39_5_checked⟩

    · exact ⟨Witness.rising, case_56_39_6_checked⟩

    · exact ⟨Witness.rising, case_56_39_7_checked⟩

    · exact ⟨Witness.rising, case_56_39_8_checked⟩

    · exact ⟨Witness.rising, case_56_39_9_checked⟩

    · exact ⟨Witness.rising, case_56_39_10_checked⟩

    · exact ⟨Witness.linear .positive case_56_39_11, case_56_39_11_checked⟩

    · exact ⟨Witness.linear .positive case_56_39_12, case_56_39_12_checked⟩

    · exact ⟨Witness.linear .positive case_56_39_13, case_56_39_13_checked⟩

    · exact ⟨Witness.linear .positive case_56_39_14, case_56_39_14_checked⟩

    · exact ⟨Witness.linear .positive case_56_39_15, case_56_39_15_checked⟩

    · exact ⟨Witness.linear .positive case_56_39_16, case_56_39_16_checked⟩

    · exact ⟨Witness.linear .positive case_56_39_17, case_56_39_17_checked⟩

    · exact ⟨Witness.linear .positive case_56_39_18, case_56_39_18_checked⟩

    · exact ⟨Witness.linear .conditional case_56_39_19, case_56_39_19_checked⟩

    · exact ⟨Witness.linear .conditional case_56_39_20, case_56_39_20_checked⟩

    · exact ⟨Witness.linear .conditional case_56_39_21, case_56_39_21_checked⟩

    · exact ⟨Witness.linear .conditional case_56_39_22, case_56_39_22_checked⟩

    · exact ⟨Witness.linear .conditional case_56_39_23, case_56_39_23_checked⟩

    · exact ⟨Witness.linear .conditional case_56_39_24, case_56_39_24_checked⟩

    · exact ⟨Witness.linear .negative case_56_39_25, case_56_39_25_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_56_40_1_checked⟩

    · exact ⟨Witness.rising, case_56_40_2_checked⟩

    · exact ⟨Witness.rising, case_56_40_3_checked⟩

    · exact ⟨Witness.rising, case_56_40_4_checked⟩

    · exact ⟨Witness.rising, case_56_40_5_checked⟩

    · exact ⟨Witness.rising, case_56_40_6_checked⟩

    · exact ⟨Witness.rising, case_56_40_7_checked⟩

    · exact ⟨Witness.rising, case_56_40_8_checked⟩

    · exact ⟨Witness.rising, case_56_40_9_checked⟩

    · exact ⟨Witness.rising, case_56_40_10_checked⟩

    · exact ⟨Witness.linear .positive case_56_40_11, case_56_40_11_checked⟩

    · exact ⟨Witness.linear .positive case_56_40_12, case_56_40_12_checked⟩

    · exact ⟨Witness.linear .positive case_56_40_13, case_56_40_13_checked⟩

    · exact ⟨Witness.linear .positive case_56_40_14, case_56_40_14_checked⟩

    · exact ⟨Witness.linear .positive case_56_40_15, case_56_40_15_checked⟩

    · exact ⟨Witness.linear .positive case_56_40_16, case_56_40_16_checked⟩

    · exact ⟨Witness.linear .positive case_56_40_17, case_56_40_17_checked⟩

    · exact ⟨Witness.linear .positive case_56_40_18, case_56_40_18_checked⟩

    · exact ⟨Witness.linear .conditional case_56_40_19, case_56_40_19_checked⟩

    · exact ⟨Witness.linear .conditional case_56_40_20, case_56_40_20_checked⟩

    · exact ⟨Witness.linear .conditional case_56_40_21, case_56_40_21_checked⟩

    · exact ⟨Witness.linear .conditional case_56_40_22, case_56_40_22_checked⟩

    · exact ⟨Witness.linear .conditional case_56_40_23, case_56_40_23_checked⟩

    · exact ⟨Witness.linear .conditional case_56_40_24, case_56_40_24_checked⟩

    · exact ⟨Witness.linear .negative case_56_40_25, case_56_40_25_checked⟩

    · exact ⟨Witness.linear .negative case_56_40_26, case_56_40_26_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_56_41_1_checked⟩

    · exact ⟨Witness.rising, case_56_41_2_checked⟩

    · exact ⟨Witness.rising, case_56_41_3_checked⟩

    · exact ⟨Witness.rising, case_56_41_4_checked⟩

    · exact ⟨Witness.rising, case_56_41_5_checked⟩

    · exact ⟨Witness.rising, case_56_41_6_checked⟩

    · exact ⟨Witness.rising, case_56_41_7_checked⟩

    · exact ⟨Witness.rising, case_56_41_8_checked⟩

    · exact ⟨Witness.rising, case_56_41_9_checked⟩

    · exact ⟨Witness.linear .positive case_56_41_10, case_56_41_10_checked⟩

    · exact ⟨Witness.linear .positive case_56_41_11, case_56_41_11_checked⟩

    · exact ⟨Witness.linear .positive case_56_41_12, case_56_41_12_checked⟩

    · exact ⟨Witness.linear .positive case_56_41_13, case_56_41_13_checked⟩

    · exact ⟨Witness.linear .positive case_56_41_14, case_56_41_14_checked⟩

    · exact ⟨Witness.linear .positive case_56_41_15, case_56_41_15_checked⟩

    · exact ⟨Witness.linear .positive case_56_41_16, case_56_41_16_checked⟩

    · exact ⟨Witness.linear .positive case_56_41_17, case_56_41_17_checked⟩

    · exact ⟨Witness.linear .positive case_56_41_18, case_56_41_18_checked⟩

    · exact ⟨Witness.linear .positive case_56_41_19, case_56_41_19_checked⟩

    · exact ⟨Witness.linear .conditional case_56_41_20, case_56_41_20_checked⟩

    · exact ⟨Witness.linear .conditional case_56_41_21, case_56_41_21_checked⟩

    · exact ⟨Witness.linear .conditional case_56_41_22, case_56_41_22_checked⟩

    · exact ⟨Witness.linear .conditional case_56_41_23, case_56_41_23_checked⟩

    · exact ⟨Witness.linear .conditional case_56_41_24, case_56_41_24_checked⟩

    · exact ⟨Witness.linear .negative case_56_41_25, case_56_41_25_checked⟩

    · exact ⟨Witness.linear .negative case_56_41_26, case_56_41_26_checked⟩

  · have hkHi : k ≤ 27 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_56_42_1_checked⟩

    · exact ⟨Witness.rising, case_56_42_2_checked⟩

    · exact ⟨Witness.rising, case_56_42_3_checked⟩

    · exact ⟨Witness.rising, case_56_42_4_checked⟩

    · exact ⟨Witness.rising, case_56_42_5_checked⟩

    · exact ⟨Witness.rising, case_56_42_6_checked⟩

    · exact ⟨Witness.rising, case_56_42_7_checked⟩

    · exact ⟨Witness.rising, case_56_42_8_checked⟩

    · exact ⟨Witness.rising, case_56_42_9_checked⟩

    · exact ⟨Witness.linear .positive case_56_42_10, case_56_42_10_checked⟩

    · exact ⟨Witness.linear .positive case_56_42_11, case_56_42_11_checked⟩

    · exact ⟨Witness.linear .positive case_56_42_12, case_56_42_12_checked⟩

    · exact ⟨Witness.linear .positive case_56_42_13, case_56_42_13_checked⟩

    · exact ⟨Witness.linear .positive case_56_42_14, case_56_42_14_checked⟩

    · exact ⟨Witness.linear .positive case_56_42_15, case_56_42_15_checked⟩

    · exact ⟨Witness.linear .positive case_56_42_16, case_56_42_16_checked⟩

    · exact ⟨Witness.linear .positive case_56_42_17, case_56_42_17_checked⟩

    · exact ⟨Witness.linear .positive case_56_42_18, case_56_42_18_checked⟩

    · exact ⟨Witness.linear .positive case_56_42_19, case_56_42_19_checked⟩

    · exact ⟨Witness.linear .positive case_56_42_20, case_56_42_20_checked⟩

    · exact ⟨Witness.linear .conditional case_56_42_21, case_56_42_21_checked⟩

    · exact ⟨Witness.linear .conditional case_56_42_22, case_56_42_22_checked⟩

    · exact ⟨Witness.linear .conditional case_56_42_23, case_56_42_23_checked⟩

    · exact ⟨Witness.linear .conditional case_56_42_24, case_56_42_24_checked⟩

    · exact ⟨Witness.linear .negative case_56_42_25, case_56_42_25_checked⟩

    · exact ⟨Witness.linear .negative case_56_42_26, case_56_42_26_checked⟩

    · exact ⟨Witness.linear .negative case_56_42_27, case_56_42_27_checked⟩

  · have hkHi : k ≤ 28 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_56_43_1_checked⟩

    · exact ⟨Witness.rising, case_56_43_2_checked⟩

    · exact ⟨Witness.rising, case_56_43_3_checked⟩

    · exact ⟨Witness.rising, case_56_43_4_checked⟩

    · exact ⟨Witness.rising, case_56_43_5_checked⟩

    · exact ⟨Witness.rising, case_56_43_6_checked⟩

    · exact ⟨Witness.rising, case_56_43_7_checked⟩

    · exact ⟨Witness.rising, case_56_43_8_checked⟩

    · exact ⟨Witness.rising, case_56_43_9_checked⟩

    · exact ⟨Witness.linear .positive case_56_43_10, case_56_43_10_checked⟩

    · exact ⟨Witness.linear .positive case_56_43_11, case_56_43_11_checked⟩

    · exact ⟨Witness.linear .positive case_56_43_12, case_56_43_12_checked⟩

    · exact ⟨Witness.linear .positive case_56_43_13, case_56_43_13_checked⟩

    · exact ⟨Witness.linear .positive case_56_43_14, case_56_43_14_checked⟩

    · exact ⟨Witness.linear .positive case_56_43_15, case_56_43_15_checked⟩

    · exact ⟨Witness.linear .positive case_56_43_16, case_56_43_16_checked⟩

    · exact ⟨Witness.linear .positive case_56_43_17, case_56_43_17_checked⟩

    · exact ⟨Witness.linear .positive case_56_43_18, case_56_43_18_checked⟩

    · exact ⟨Witness.linear .positive case_56_43_19, case_56_43_19_checked⟩

    · exact ⟨Witness.linear .positive case_56_43_20, case_56_43_20_checked⟩

    · exact ⟨Witness.linear .conditional case_56_43_21, case_56_43_21_checked⟩

    · exact ⟨Witness.linear .conditional case_56_43_22, case_56_43_22_checked⟩

    · exact ⟨Witness.linear .conditional case_56_43_23, case_56_43_23_checked⟩

    · exact ⟨Witness.linear .conditional case_56_43_24, case_56_43_24_checked⟩

    · exact ⟨Witness.linear .negative case_56_43_25, case_56_43_25_checked⟩

    · exact ⟨Witness.linear .negative case_56_43_26, case_56_43_26_checked⟩

    · exact ⟨Witness.linear .negative case_56_43_27, case_56_43_27_checked⟩

    · exact ⟨Witness.linear .negative case_56_43_28, case_56_43_28_checked⟩

  · have hkHi : k ≤ 28 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_56_44_1_checked⟩

    · exact ⟨Witness.rising, case_56_44_2_checked⟩

    · exact ⟨Witness.rising, case_56_44_3_checked⟩

    · exact ⟨Witness.rising, case_56_44_4_checked⟩

    · exact ⟨Witness.rising, case_56_44_5_checked⟩

    · exact ⟨Witness.rising, case_56_44_6_checked⟩

    · exact ⟨Witness.rising, case_56_44_7_checked⟩

    · exact ⟨Witness.rising, case_56_44_8_checked⟩

    · exact ⟨Witness.rising, case_56_44_9_checked⟩

    · exact ⟨Witness.linear .positive case_56_44_10, case_56_44_10_checked⟩

    · exact ⟨Witness.linear .positive case_56_44_11, case_56_44_11_checked⟩

    · exact ⟨Witness.linear .positive case_56_44_12, case_56_44_12_checked⟩

    · exact ⟨Witness.linear .positive case_56_44_13, case_56_44_13_checked⟩

    · exact ⟨Witness.linear .positive case_56_44_14, case_56_44_14_checked⟩

    · exact ⟨Witness.linear .positive case_56_44_15, case_56_44_15_checked⟩

    · exact ⟨Witness.linear .positive case_56_44_16, case_56_44_16_checked⟩

    · exact ⟨Witness.linear .positive case_56_44_17, case_56_44_17_checked⟩

    · exact ⟨Witness.linear .positive case_56_44_18, case_56_44_18_checked⟩

    · exact ⟨Witness.linear .positive case_56_44_19, case_56_44_19_checked⟩

    · exact ⟨Witness.linear .positive case_56_44_20, case_56_44_20_checked⟩

    · exact ⟨Witness.linear .positive case_56_44_21, case_56_44_21_checked⟩

    · exact ⟨Witness.linear .conditional case_56_44_22, case_56_44_22_checked⟩

    · exact ⟨Witness.linear .conditional case_56_44_23, case_56_44_23_checked⟩

    · exact ⟨Witness.linear .conditional case_56_44_24, case_56_44_24_checked⟩

    · exact ⟨Witness.linear .negative case_56_44_25, case_56_44_25_checked⟩

    · exact ⟨Witness.linear .negative case_56_44_26, case_56_44_26_checked⟩

    · exact ⟨Witness.linear .negative case_56_44_27, case_56_44_27_checked⟩

    · exact ⟨Witness.linear .negative case_56_44_28, case_56_44_28_checked⟩

  · have hkHi : k ≤ 29 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_56_45_1_checked⟩

    · exact ⟨Witness.rising, case_56_45_2_checked⟩

    · exact ⟨Witness.rising, case_56_45_3_checked⟩

    · exact ⟨Witness.rising, case_56_45_4_checked⟩

    · exact ⟨Witness.rising, case_56_45_5_checked⟩

    · exact ⟨Witness.rising, case_56_45_6_checked⟩

    · exact ⟨Witness.rising, case_56_45_7_checked⟩

    · exact ⟨Witness.rising, case_56_45_8_checked⟩

    · exact ⟨Witness.rising, case_56_45_9_checked⟩

    · exact ⟨Witness.linear .positive case_56_45_10, case_56_45_10_checked⟩

    · exact ⟨Witness.linear .positive case_56_45_11, case_56_45_11_checked⟩

    · exact ⟨Witness.linear .positive case_56_45_12, case_56_45_12_checked⟩

    · exact ⟨Witness.linear .positive case_56_45_13, case_56_45_13_checked⟩

    · exact ⟨Witness.linear .positive case_56_45_14, case_56_45_14_checked⟩

    · exact ⟨Witness.linear .positive case_56_45_15, case_56_45_15_checked⟩

    · exact ⟨Witness.linear .positive case_56_45_16, case_56_45_16_checked⟩

    · exact ⟨Witness.linear .positive case_56_45_17, case_56_45_17_checked⟩

    · exact ⟨Witness.linear .positive case_56_45_18, case_56_45_18_checked⟩

    · exact ⟨Witness.linear .positive case_56_45_19, case_56_45_19_checked⟩

    · exact ⟨Witness.linear .positive case_56_45_20, case_56_45_20_checked⟩

    · exact ⟨Witness.linear .positive case_56_45_21, case_56_45_21_checked⟩

    · exact ⟨Witness.linear .positive case_56_45_22, case_56_45_22_checked⟩

    · exact ⟨Witness.linear .conditional case_56_45_23, case_56_45_23_checked⟩

    · exact ⟨Witness.linear .conditional case_56_45_24, case_56_45_24_checked⟩

    · exact ⟨Witness.linear .conditional case_56_45_25, case_56_45_25_checked⟩

    · exact ⟨Witness.linear .negative case_56_45_26, case_56_45_26_checked⟩

    · exact ⟨Witness.linear .negative case_56_45_27, case_56_45_27_checked⟩

    · exact ⟨Witness.linear .negative case_56_45_28, case_56_45_28_checked⟩

    · exact ⟨Witness.linear .negative case_56_45_29, case_56_45_29_checked⟩

  · have hkHi : k ≤ 30 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_56_46_1_checked⟩

    · exact ⟨Witness.rising, case_56_46_2_checked⟩

    · exact ⟨Witness.rising, case_56_46_3_checked⟩

    · exact ⟨Witness.rising, case_56_46_4_checked⟩

    · exact ⟨Witness.rising, case_56_46_5_checked⟩

    · exact ⟨Witness.rising, case_56_46_6_checked⟩

    · exact ⟨Witness.rising, case_56_46_7_checked⟩

    · exact ⟨Witness.rising, case_56_46_8_checked⟩

    · exact ⟨Witness.rising, case_56_46_9_checked⟩

    · exact ⟨Witness.linear .positive case_56_46_10, case_56_46_10_checked⟩

    · exact ⟨Witness.linear .positive case_56_46_11, case_56_46_11_checked⟩

    · exact ⟨Witness.linear .positive case_56_46_12, case_56_46_12_checked⟩

    · exact ⟨Witness.linear .positive case_56_46_13, case_56_46_13_checked⟩

    · exact ⟨Witness.linear .positive case_56_46_14, case_56_46_14_checked⟩

    · exact ⟨Witness.linear .positive case_56_46_15, case_56_46_15_checked⟩

    · exact ⟨Witness.linear .positive case_56_46_16, case_56_46_16_checked⟩

    · exact ⟨Witness.linear .positive case_56_46_17, case_56_46_17_checked⟩

    · exact ⟨Witness.linear .positive case_56_46_18, case_56_46_18_checked⟩

    · exact ⟨Witness.linear .positive case_56_46_19, case_56_46_19_checked⟩

    · exact ⟨Witness.linear .positive case_56_46_20, case_56_46_20_checked⟩

    · exact ⟨Witness.linear .positive case_56_46_21, case_56_46_21_checked⟩

    · exact ⟨Witness.linear .positive case_56_46_22, case_56_46_22_checked⟩

    · exact ⟨Witness.linear .conditional case_56_46_23, case_56_46_23_checked⟩

    · exact ⟨Witness.linear .conditional case_56_46_24, case_56_46_24_checked⟩

    · exact ⟨Witness.linear .conditional case_56_46_25, case_56_46_25_checked⟩

    · exact ⟨Witness.linear .negative case_56_46_26, case_56_46_26_checked⟩

    · exact ⟨Witness.linear .negative case_56_46_27, case_56_46_27_checked⟩

    · exact ⟨Witness.linear .negative case_56_46_28, case_56_46_28_checked⟩

    · exact ⟨Witness.linear .negative case_56_46_29, case_56_46_29_checked⟩

    · exact ⟨Witness.linear .negative case_56_46_30, case_56_46_30_checked⟩

  · have hkHi : k ≤ 30 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_56_47_1_checked⟩

    · exact ⟨Witness.rising, case_56_47_2_checked⟩

    · exact ⟨Witness.rising, case_56_47_3_checked⟩

    · exact ⟨Witness.rising, case_56_47_4_checked⟩

    · exact ⟨Witness.rising, case_56_47_5_checked⟩

    · exact ⟨Witness.rising, case_56_47_6_checked⟩

    · exact ⟨Witness.rising, case_56_47_7_checked⟩

    · exact ⟨Witness.rising, case_56_47_8_checked⟩

    · exact ⟨Witness.rising, case_56_47_9_checked⟩

    · exact ⟨Witness.linear .positive case_56_47_10, case_56_47_10_checked⟩

    · exact ⟨Witness.linear .positive case_56_47_11, case_56_47_11_checked⟩

    · exact ⟨Witness.linear .positive case_56_47_12, case_56_47_12_checked⟩

    · exact ⟨Witness.linear .positive case_56_47_13, case_56_47_13_checked⟩

    · exact ⟨Witness.linear .positive case_56_47_14, case_56_47_14_checked⟩

    · exact ⟨Witness.linear .positive case_56_47_15, case_56_47_15_checked⟩

    · exact ⟨Witness.linear .positive case_56_47_16, case_56_47_16_checked⟩

    · exact ⟨Witness.linear .positive case_56_47_17, case_56_47_17_checked⟩

    · exact ⟨Witness.linear .positive case_56_47_18, case_56_47_18_checked⟩

    · exact ⟨Witness.linear .positive case_56_47_19, case_56_47_19_checked⟩

    · exact ⟨Witness.linear .positive case_56_47_20, case_56_47_20_checked⟩

    · exact ⟨Witness.linear .positive case_56_47_21, case_56_47_21_checked⟩

    · exact ⟨Witness.linear .positive case_56_47_22, case_56_47_22_checked⟩

    · exact ⟨Witness.linear .positive case_56_47_23, case_56_47_23_checked⟩

    · exact ⟨Witness.linear .conditional case_56_47_24, case_56_47_24_checked⟩

    · exact ⟨Witness.linear .conditional case_56_47_25, case_56_47_25_checked⟩

    · exact ⟨Witness.linear .negative case_56_47_26, case_56_47_26_checked⟩

    · exact ⟨Witness.linear .negative case_56_47_27, case_56_47_27_checked⟩

    · exact ⟨Witness.linear .negative case_56_47_28, case_56_47_28_checked⟩

    · exact ⟨Witness.linear .negative case_56_47_29, case_56_47_29_checked⟩

    · exact ⟨Witness.linear .negative case_56_47_30, case_56_47_30_checked⟩

  · have hkHi : k ≤ 31 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_56_48_1_checked⟩

    · exact ⟨Witness.rising, case_56_48_2_checked⟩

    · exact ⟨Witness.rising, case_56_48_3_checked⟩

    · exact ⟨Witness.rising, case_56_48_4_checked⟩

    · exact ⟨Witness.rising, case_56_48_5_checked⟩

    · exact ⟨Witness.rising, case_56_48_6_checked⟩

    · exact ⟨Witness.rising, case_56_48_7_checked⟩

    · exact ⟨Witness.rising, case_56_48_8_checked⟩

    · exact ⟨Witness.rising, case_56_48_9_checked⟩

    · exact ⟨Witness.linear .positive case_56_48_10, case_56_48_10_checked⟩

    · exact ⟨Witness.linear .positive case_56_48_11, case_56_48_11_checked⟩

    · exact ⟨Witness.linear .positive case_56_48_12, case_56_48_12_checked⟩

    · exact ⟨Witness.linear .positive case_56_48_13, case_56_48_13_checked⟩

    · exact ⟨Witness.linear .positive case_56_48_14, case_56_48_14_checked⟩

    · exact ⟨Witness.linear .positive case_56_48_15, case_56_48_15_checked⟩

    · exact ⟨Witness.linear .positive case_56_48_16, case_56_48_16_checked⟩

    · exact ⟨Witness.linear .positive case_56_48_17, case_56_48_17_checked⟩

    · exact ⟨Witness.linear .positive case_56_48_18, case_56_48_18_checked⟩

    · exact ⟨Witness.linear .positive case_56_48_19, case_56_48_19_checked⟩

    · exact ⟨Witness.linear .positive case_56_48_20, case_56_48_20_checked⟩

    · exact ⟨Witness.linear .positive case_56_48_21, case_56_48_21_checked⟩

    · exact ⟨Witness.linear .positive case_56_48_22, case_56_48_22_checked⟩

    · exact ⟨Witness.linear .positive case_56_48_23, case_56_48_23_checked⟩

    · exact ⟨Witness.linear .conditional case_56_48_24, case_56_48_24_checked⟩

    · exact ⟨Witness.linear .conditional case_56_48_25, case_56_48_25_checked⟩

    · exact ⟨Witness.linear .negative case_56_48_26, case_56_48_26_checked⟩

    · exact ⟨Witness.linear .negative case_56_48_27, case_56_48_27_checked⟩

    · exact ⟨Witness.linear .negative case_56_48_28, case_56_48_28_checked⟩

    · exact ⟨Witness.linear .negative case_56_48_29, case_56_48_29_checked⟩

    · exact ⟨Witness.linear .negative case_56_48_30, case_56_48_30_checked⟩

    · exact ⟨Witness.linear .negative case_56_48_31, case_56_48_31_checked⟩

  · have hkHi : k ≤ 32 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_56_49_1_checked⟩

    · exact ⟨Witness.rising, case_56_49_2_checked⟩

    · exact ⟨Witness.rising, case_56_49_3_checked⟩

    · exact ⟨Witness.rising, case_56_49_4_checked⟩

    · exact ⟨Witness.rising, case_56_49_5_checked⟩

    · exact ⟨Witness.rising, case_56_49_6_checked⟩

    · exact ⟨Witness.rising, case_56_49_7_checked⟩

    · exact ⟨Witness.rising, case_56_49_8_checked⟩

    · exact ⟨Witness.rising, case_56_49_9_checked⟩

    · exact ⟨Witness.linear .positive case_56_49_10, case_56_49_10_checked⟩

    · exact ⟨Witness.linear .positive case_56_49_11, case_56_49_11_checked⟩

    · exact ⟨Witness.linear .positive case_56_49_12, case_56_49_12_checked⟩

    · exact ⟨Witness.linear .positive case_56_49_13, case_56_49_13_checked⟩

    · exact ⟨Witness.linear .positive case_56_49_14, case_56_49_14_checked⟩

    · exact ⟨Witness.linear .positive case_56_49_15, case_56_49_15_checked⟩

    · exact ⟨Witness.linear .positive case_56_49_16, case_56_49_16_checked⟩

    · exact ⟨Witness.linear .positive case_56_49_17, case_56_49_17_checked⟩

    · exact ⟨Witness.linear .positive case_56_49_18, case_56_49_18_checked⟩

    · exact ⟨Witness.linear .positive case_56_49_19, case_56_49_19_checked⟩

    · exact ⟨Witness.linear .positive case_56_49_20, case_56_49_20_checked⟩

    · exact ⟨Witness.linear .positive case_56_49_21, case_56_49_21_checked⟩

    · exact ⟨Witness.linear .positive case_56_49_22, case_56_49_22_checked⟩

    · exact ⟨Witness.linear .positive case_56_49_23, case_56_49_23_checked⟩

    · exact ⟨Witness.linear .positive case_56_49_24, case_56_49_24_checked⟩

    · exact ⟨Witness.linear .conditional case_56_49_25, case_56_49_25_checked⟩

    · exact ⟨Witness.linear .negative case_56_49_26, case_56_49_26_checked⟩

    · exact ⟨Witness.linear .negative case_56_49_27, case_56_49_27_checked⟩

    · exact ⟨Witness.linear .negative case_56_49_28, case_56_49_28_checked⟩

    · exact ⟨Witness.linear .negative case_56_49_29, case_56_49_29_checked⟩

    · exact ⟨Witness.linear .negative case_56_49_30, case_56_49_30_checked⟩

    · exact ⟨Witness.linear .negative case_56_49_31, case_56_49_31_checked⟩

    · exact ⟨Witness.linear .negative case_56_49_32, case_56_49_32_checked⟩

  · have hkHi : k ≤ 32 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_56_50_1_checked⟩

    · exact ⟨Witness.rising, case_56_50_2_checked⟩

    · exact ⟨Witness.rising, case_56_50_3_checked⟩

    · exact ⟨Witness.rising, case_56_50_4_checked⟩

    · exact ⟨Witness.rising, case_56_50_5_checked⟩

    · exact ⟨Witness.rising, case_56_50_6_checked⟩

    · exact ⟨Witness.rising, case_56_50_7_checked⟩

    · exact ⟨Witness.rising, case_56_50_8_checked⟩

    · exact ⟨Witness.rising, case_56_50_9_checked⟩

    · exact ⟨Witness.linear .positive case_56_50_10, case_56_50_10_checked⟩

    · exact ⟨Witness.linear .positive case_56_50_11, case_56_50_11_checked⟩

    · exact ⟨Witness.linear .positive case_56_50_12, case_56_50_12_checked⟩

    · exact ⟨Witness.linear .positive case_56_50_13, case_56_50_13_checked⟩

    · exact ⟨Witness.linear .positive case_56_50_14, case_56_50_14_checked⟩

    · exact ⟨Witness.linear .positive case_56_50_15, case_56_50_15_checked⟩

    · exact ⟨Witness.linear .positive case_56_50_16, case_56_50_16_checked⟩

    · exact ⟨Witness.linear .positive case_56_50_17, case_56_50_17_checked⟩

    · exact ⟨Witness.linear .positive case_56_50_18, case_56_50_18_checked⟩

    · exact ⟨Witness.linear .positive case_56_50_19, case_56_50_19_checked⟩

    · exact ⟨Witness.linear .positive case_56_50_20, case_56_50_20_checked⟩

    · exact ⟨Witness.linear .positive case_56_50_21, case_56_50_21_checked⟩

    · exact ⟨Witness.linear .positive case_56_50_22, case_56_50_22_checked⟩

    · exact ⟨Witness.linear .positive case_56_50_23, case_56_50_23_checked⟩

    · exact ⟨Witness.linear .positive case_56_50_24, case_56_50_24_checked⟩

    · exact ⟨Witness.linear .positive case_56_50_25, case_56_50_25_checked⟩

    · exact ⟨Witness.linear .negative case_56_50_26, case_56_50_26_checked⟩

    · exact ⟨Witness.linear .negative case_56_50_27, case_56_50_27_checked⟩

    · exact ⟨Witness.linear .negative case_56_50_28, case_56_50_28_checked⟩

    · exact ⟨Witness.linear .negative case_56_50_29, case_56_50_29_checked⟩

    · exact ⟨Witness.linear .negative case_56_50_30, case_56_50_30_checked⟩

    · exact ⟨Witness.linear .negative case_56_50_31, case_56_50_31_checked⟩

    · exact ⟨Witness.linear .negative case_56_50_32, case_56_50_32_checked⟩

  · have hkHi : k ≤ 33 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_56_51_1_checked⟩

    · exact ⟨Witness.rising, case_56_51_2_checked⟩

    · exact ⟨Witness.rising, case_56_51_3_checked⟩

    · exact ⟨Witness.rising, case_56_51_4_checked⟩

    · exact ⟨Witness.rising, case_56_51_5_checked⟩

    · exact ⟨Witness.rising, case_56_51_6_checked⟩

    · exact ⟨Witness.rising, case_56_51_7_checked⟩

    · exact ⟨Witness.rising, case_56_51_8_checked⟩

    · exact ⟨Witness.rising, case_56_51_9_checked⟩

    · exact ⟨Witness.linear .positive case_56_51_10, case_56_51_10_checked⟩

    · exact ⟨Witness.linear .positive case_56_51_11, case_56_51_11_checked⟩

    · exact ⟨Witness.linear .positive case_56_51_12, case_56_51_12_checked⟩

    · exact ⟨Witness.linear .positive case_56_51_13, case_56_51_13_checked⟩

    · exact ⟨Witness.linear .positive case_56_51_14, case_56_51_14_checked⟩

    · exact ⟨Witness.linear .positive case_56_51_15, case_56_51_15_checked⟩

    · exact ⟨Witness.linear .positive case_56_51_16, case_56_51_16_checked⟩

    · exact ⟨Witness.linear .positive case_56_51_17, case_56_51_17_checked⟩

    · exact ⟨Witness.linear .positive case_56_51_18, case_56_51_18_checked⟩

    · exact ⟨Witness.linear .positive case_56_51_19, case_56_51_19_checked⟩

    · exact ⟨Witness.linear .positive case_56_51_20, case_56_51_20_checked⟩

    · exact ⟨Witness.linear .positive case_56_51_21, case_56_51_21_checked⟩

    · exact ⟨Witness.linear .positive case_56_51_22, case_56_51_22_checked⟩

    · exact ⟨Witness.linear .positive case_56_51_23, case_56_51_23_checked⟩

    · exact ⟨Witness.linear .positive case_56_51_24, case_56_51_24_checked⟩

    · exact ⟨Witness.linear .positive case_56_51_25, case_56_51_25_checked⟩

    · exact ⟨Witness.linear .conditional case_56_51_26, case_56_51_26_checked⟩

    · exact ⟨Witness.linear .negative case_56_51_27, case_56_51_27_checked⟩

    · exact ⟨Witness.linear .negative case_56_51_28, case_56_51_28_checked⟩

    · exact ⟨Witness.linear .negative case_56_51_29, case_56_51_29_checked⟩

    · exact ⟨Witness.linear .negative case_56_51_30, case_56_51_30_checked⟩

    · exact ⟨Witness.linear .negative case_56_51_31, case_56_51_31_checked⟩

    · exact ⟨Witness.linear .negative case_56_51_32, case_56_51_32_checked⟩

    · exact ⟨Witness.linear .negative case_56_51_33, case_56_51_33_checked⟩

  · have hkHi : k ≤ 34 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_56_52_1_checked⟩

    · exact ⟨Witness.rising, case_56_52_2_checked⟩

    · exact ⟨Witness.rising, case_56_52_3_checked⟩

    · exact ⟨Witness.rising, case_56_52_4_checked⟩

    · exact ⟨Witness.rising, case_56_52_5_checked⟩

    · exact ⟨Witness.rising, case_56_52_6_checked⟩

    · exact ⟨Witness.rising, case_56_52_7_checked⟩

    · exact ⟨Witness.rising, case_56_52_8_checked⟩

    · exact ⟨Witness.rising, case_56_52_9_checked⟩

    · exact ⟨Witness.linear .positive case_56_52_10, case_56_52_10_checked⟩

    · exact ⟨Witness.linear .positive case_56_52_11, case_56_52_11_checked⟩

    · exact ⟨Witness.linear .positive case_56_52_12, case_56_52_12_checked⟩

    · exact ⟨Witness.linear .positive case_56_52_13, case_56_52_13_checked⟩

    · exact ⟨Witness.linear .positive case_56_52_14, case_56_52_14_checked⟩

    · exact ⟨Witness.linear .positive case_56_52_15, case_56_52_15_checked⟩

    · exact ⟨Witness.linear .positive case_56_52_16, case_56_52_16_checked⟩

    · exact ⟨Witness.linear .positive case_56_52_17, case_56_52_17_checked⟩

    · exact ⟨Witness.linear .positive case_56_52_18, case_56_52_18_checked⟩

    · exact ⟨Witness.linear .positive case_56_52_19, case_56_52_19_checked⟩

    · exact ⟨Witness.linear .positive case_56_52_20, case_56_52_20_checked⟩

    · exact ⟨Witness.linear .positive case_56_52_21, case_56_52_21_checked⟩

    · exact ⟨Witness.linear .positive case_56_52_22, case_56_52_22_checked⟩

    · exact ⟨Witness.linear .positive case_56_52_23, case_56_52_23_checked⟩

    · exact ⟨Witness.linear .positive case_56_52_24, case_56_52_24_checked⟩

    · exact ⟨Witness.linear .positive case_56_52_25, case_56_52_25_checked⟩

    · exact ⟨Witness.linear .positive case_56_52_26, case_56_52_26_checked⟩

    · exact ⟨Witness.linear .negative case_56_52_27, case_56_52_27_checked⟩

    · exact ⟨Witness.linear .negative case_56_52_28, case_56_52_28_checked⟩

    · exact ⟨Witness.linear .negative case_56_52_29, case_56_52_29_checked⟩

    · exact ⟨Witness.linear .negative case_56_52_30, case_56_52_30_checked⟩

    · exact ⟨Witness.linear .negative case_56_52_31, case_56_52_31_checked⟩

    · exact ⟨Witness.linear .negative case_56_52_32, case_56_52_32_checked⟩

    · exact ⟨Witness.linear .negative case_56_52_33, case_56_52_33_checked⟩

    · exact ⟨Witness.linear .negative case_56_52_34, case_56_52_34_checked⟩

  · have hkHi : k ≤ 34 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_56_53_1_checked⟩

    · exact ⟨Witness.rising, case_56_53_2_checked⟩

    · exact ⟨Witness.rising, case_56_53_3_checked⟩

    · exact ⟨Witness.rising, case_56_53_4_checked⟩

    · exact ⟨Witness.rising, case_56_53_5_checked⟩

    · exact ⟨Witness.rising, case_56_53_6_checked⟩

    · exact ⟨Witness.rising, case_56_53_7_checked⟩

    · exact ⟨Witness.rising, case_56_53_8_checked⟩

    · exact ⟨Witness.rising, case_56_53_9_checked⟩

    · exact ⟨Witness.linear .positive case_56_53_10, case_56_53_10_checked⟩

    · exact ⟨Witness.linear .positive case_56_53_11, case_56_53_11_checked⟩

    · exact ⟨Witness.linear .positive case_56_53_12, case_56_53_12_checked⟩

    · exact ⟨Witness.linear .positive case_56_53_13, case_56_53_13_checked⟩

    · exact ⟨Witness.linear .positive case_56_53_14, case_56_53_14_checked⟩

    · exact ⟨Witness.linear .positive case_56_53_15, case_56_53_15_checked⟩

    · exact ⟨Witness.linear .positive case_56_53_16, case_56_53_16_checked⟩

    · exact ⟨Witness.linear .positive case_56_53_17, case_56_53_17_checked⟩

    · exact ⟨Witness.linear .positive case_56_53_18, case_56_53_18_checked⟩

    · exact ⟨Witness.linear .positive case_56_53_19, case_56_53_19_checked⟩

    · exact ⟨Witness.linear .positive case_56_53_20, case_56_53_20_checked⟩

    · exact ⟨Witness.linear .positive case_56_53_21, case_56_53_21_checked⟩

    · exact ⟨Witness.linear .positive case_56_53_22, case_56_53_22_checked⟩

    · exact ⟨Witness.linear .positive case_56_53_23, case_56_53_23_checked⟩

    · exact ⟨Witness.linear .positive case_56_53_24, case_56_53_24_checked⟩

    · exact ⟨Witness.linear .positive case_56_53_25, case_56_53_25_checked⟩

    · exact ⟨Witness.linear .positive case_56_53_26, case_56_53_26_checked⟩

    · exact ⟨Witness.linear .negative case_56_53_27, case_56_53_27_checked⟩

    · exact ⟨Witness.linear .negative case_56_53_28, case_56_53_28_checked⟩

    · exact ⟨Witness.linear .negative case_56_53_29, case_56_53_29_checked⟩

    · exact ⟨Witness.linear .negative case_56_53_30, case_56_53_30_checked⟩

    · exact ⟨Witness.linear .negative case_56_53_31, case_56_53_31_checked⟩

    · exact ⟨Witness.linear .negative case_56_53_32, case_56_53_32_checked⟩

    · exact ⟨Witness.linear .negative case_56_53_33, case_56_53_33_checked⟩

    · exact ⟨Witness.linear .negative case_56_53_34, case_56_53_34_checked⟩

  · have hkHi : k ≤ 35 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_56_54_1_checked⟩

    · exact ⟨Witness.rising, case_56_54_2_checked⟩

    · exact ⟨Witness.rising, case_56_54_3_checked⟩

    · exact ⟨Witness.rising, case_56_54_4_checked⟩

    · exact ⟨Witness.rising, case_56_54_5_checked⟩

    · exact ⟨Witness.rising, case_56_54_6_checked⟩

    · exact ⟨Witness.rising, case_56_54_7_checked⟩

    · exact ⟨Witness.rising, case_56_54_8_checked⟩

    · exact ⟨Witness.rising, case_56_54_9_checked⟩

    · exact ⟨Witness.linear .positive case_56_54_10, case_56_54_10_checked⟩

    · exact ⟨Witness.linear .positive case_56_54_11, case_56_54_11_checked⟩

    · exact ⟨Witness.linear .positive case_56_54_12, case_56_54_12_checked⟩

    · exact ⟨Witness.linear .positive case_56_54_13, case_56_54_13_checked⟩

    · exact ⟨Witness.linear .positive case_56_54_14, case_56_54_14_checked⟩

    · exact ⟨Witness.linear .positive case_56_54_15, case_56_54_15_checked⟩

    · exact ⟨Witness.linear .positive case_56_54_16, case_56_54_16_checked⟩

    · exact ⟨Witness.linear .positive case_56_54_17, case_56_54_17_checked⟩

    · exact ⟨Witness.linear .positive case_56_54_18, case_56_54_18_checked⟩

    · exact ⟨Witness.linear .positive case_56_54_19, case_56_54_19_checked⟩

    · exact ⟨Witness.linear .positive case_56_54_20, case_56_54_20_checked⟩

    · exact ⟨Witness.linear .positive case_56_54_21, case_56_54_21_checked⟩

    · exact ⟨Witness.linear .positive case_56_54_22, case_56_54_22_checked⟩

    · exact ⟨Witness.linear .positive case_56_54_23, case_56_54_23_checked⟩

    · exact ⟨Witness.linear .positive case_56_54_24, case_56_54_24_checked⟩

    · exact ⟨Witness.linear .positive case_56_54_25, case_56_54_25_checked⟩

    · exact ⟨Witness.linear .positive case_56_54_26, case_56_54_26_checked⟩

    · exact ⟨Witness.linear .positive case_56_54_27, case_56_54_27_checked⟩

    · exact ⟨Witness.linear .negative case_56_54_28, case_56_54_28_checked⟩

    · exact ⟨Witness.linear .negative case_56_54_29, case_56_54_29_checked⟩

    · exact ⟨Witness.linear .negative case_56_54_30, case_56_54_30_checked⟩

    · exact ⟨Witness.linear .negative case_56_54_31, case_56_54_31_checked⟩

    · exact ⟨Witness.linear .negative case_56_54_32, case_56_54_32_checked⟩

    · exact ⟨Witness.linear .negative case_56_54_33, case_56_54_33_checked⟩

    · exact ⟨Witness.linear .negative case_56_54_34, case_56_54_34_checked⟩

    · exact ⟨Witness.linear .negative case_56_54_35, case_56_54_35_checked⟩

  · have hkHi : k ≤ 36 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_56_55_1_checked⟩

    · exact ⟨Witness.rising, case_56_55_2_checked⟩

    · exact ⟨Witness.rising, case_56_55_3_checked⟩

    · exact ⟨Witness.rising, case_56_55_4_checked⟩

    · exact ⟨Witness.rising, case_56_55_5_checked⟩

    · exact ⟨Witness.rising, case_56_55_6_checked⟩

    · exact ⟨Witness.rising, case_56_55_7_checked⟩

    · exact ⟨Witness.rising, case_56_55_8_checked⟩

    · exact ⟨Witness.rising, case_56_55_9_checked⟩

    · exact ⟨Witness.linear .positive case_56_55_10, case_56_55_10_checked⟩

    · exact ⟨Witness.linear .positive case_56_55_11, case_56_55_11_checked⟩

    · exact ⟨Witness.linear .positive case_56_55_12, case_56_55_12_checked⟩

    · exact ⟨Witness.linear .positive case_56_55_13, case_56_55_13_checked⟩

    · exact ⟨Witness.linear .positive case_56_55_14, case_56_55_14_checked⟩

    · exact ⟨Witness.linear .positive case_56_55_15, case_56_55_15_checked⟩

    · exact ⟨Witness.linear .positive case_56_55_16, case_56_55_16_checked⟩

    · exact ⟨Witness.linear .positive case_56_55_17, case_56_55_17_checked⟩

    · exact ⟨Witness.linear .positive case_56_55_18, case_56_55_18_checked⟩

    · exact ⟨Witness.linear .positive case_56_55_19, case_56_55_19_checked⟩

    · exact ⟨Witness.linear .positive case_56_55_20, case_56_55_20_checked⟩

    · exact ⟨Witness.linear .positive case_56_55_21, case_56_55_21_checked⟩

    · exact ⟨Witness.linear .positive case_56_55_22, case_56_55_22_checked⟩

    · exact ⟨Witness.linear .positive case_56_55_23, case_56_55_23_checked⟩

    · exact ⟨Witness.linear .positive case_56_55_24, case_56_55_24_checked⟩

    · exact ⟨Witness.linear .positive case_56_55_25, case_56_55_25_checked⟩

    · exact ⟨Witness.linear .positive case_56_55_26, case_56_55_26_checked⟩

    · exact ⟨Witness.linear .positive case_56_55_27, case_56_55_27_checked⟩

    · exact ⟨Witness.linear .negative case_56_55_28, case_56_55_28_checked⟩

    · exact ⟨Witness.linear .negative case_56_55_29, case_56_55_29_checked⟩

    · exact ⟨Witness.linear .negative case_56_55_30, case_56_55_30_checked⟩

    · exact ⟨Witness.linear .negative case_56_55_31, case_56_55_31_checked⟩

    · exact ⟨Witness.linear .negative case_56_55_32, case_56_55_32_checked⟩

    · exact ⟨Witness.linear .negative case_56_55_33, case_56_55_33_checked⟩

    · exact ⟨Witness.linear .negative case_56_55_34, case_56_55_34_checked⟩

    · exact ⟨Witness.linear .negative case_56_55_35, case_56_55_35_checked⟩

    · exact ⟨Witness.linear .negative case_56_55_36, case_56_55_36_checked⟩


#print axioms coverage_56
end ForestUnimodality.FiniteRows.FiniteData
