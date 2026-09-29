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

theorem case_35_18_1_checked :
    (Witness.rising).check 35 18 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_18_2_checked :
    (Witness.rising).check 35 18 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_18_3_checked :
    (Witness.rising).check 35 18 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_18_4_checked :
    (Witness.rising).check 35 18 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_18_5_checked :
    (Witness.rising).check 35 18 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_18_6_checked :
    (Witness.rising).check 35 18 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_18_7_checked :
    (Witness.rising).check 35 18 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_18_8 : Certificate := {
  objectiveScale := 13483126800000
  eta := 35712029866312800
  rows := #[⟨.count 2, 8146431055362600⟩, ⟨.count 3, 1205431311144060⟩, ⟨.count 4, 212142168758520⟩, ⟨.count 5, 50541500809800⟩, ⟨.count 6, 17342671846500⟩, ⟨.count 7, 13453709068800⟩, ⟨.path 8, 3911010303200⟩, ⟨.path 9, 2264307285240⟩, ⟨.privateRow 8 0, 405140102640⟩, ⟨.privateRow 9 0, 226097055184⟩, ⟨.hall 6 3, 53637989405⟩, ⟨.hall 6 4, 1167856690⟩, ⟨.hall 5 6, 21945438900⟩, ⟨.hall 4 10, 102318546330⟩, ⟨.hall 7 10, 76441528800⟩, ⟨.hall 3 14, 14228698768284⟩]
  caps := #[0, 41935884905200, 0, 1241720946180, 0, 0, 51465256700, 29678345125, 0, 3336733400, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_35_18_8_checked :
    (Witness.linear .positive case_35_18_8).check 35 18 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_18_9 : Certificate := {
  objectiveScale := 924000000
  eta := 3001193395200
  rows := #[⟨.count 2, 743083941600⟩, ⟨.count 3, 132023651760⟩, ⟨.count 4, 27311684400⟩, ⟨.count 5, 6976569600⟩, ⟨.count 6, 2259457200⟩, ⟨.count 7, 958557600⟩, ⟨.count 8, 928287360⟩, ⟨.path 9, 35263800⟩, ⟨.path 10, 272764800⟩, ⟨.privateRow 7 4, 8108100⟩, ⟨.privateRow 8 2, 10090080⟩, ⟨.privateRow 9 0, 43723680⟩, ⟨.privateRow 10 0, 30270240⟩, ⟨.hall 7 3, 7137585⟩, ⟨.hall 6 5, 4715425⟩, ⟨.hall 5 8, 8439200⟩, ⟨.hall 8 9, 18162144⟩, ⟨.hall 4 11, 69652440⟩, ⟨.hall 3 14, 3366723360⟩]
  caps := #[0, 0, 0, 366005640, 68708640, 31145400, 12559800, 5773350, 0, 0, 332640, 0, 0, 0, 0, 0, 0, 0] }

theorem case_35_18_9_checked :
    (Witness.linear .positive case_35_18_9).check 35 18 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_18_10 : Certificate := {
  objectiveScale := 63000000
  eta := 306940233600
  rows := #[⟨.count 2, 90016126200⟩, ⟨.count 3, 20265925680⟩, ⟨.count 4, 5199994800⟩, ⟨.count 5, 1322521200⟩, ⟨.count 6, 409008600⟩, ⟨.count 7, 142178400⟩, ⟨.count 8, 63292320⟩, ⟨.count 9, 63292320⟩, ⟨.path 11, 15750000⟩, ⟨.privateRow 11 0, 1965600⟩, ⟨.privateRow 11 4, 573300⟩, ⟨.privateRow 11 5, 273000⟩, ⟨.privateRow 11 6, 245700⟩, ⟨.privateRow 12 0, 3260400⟩, ⟨.privateRow 12 4, 1501500⟩, ⟨.hall 9 2, 1066520⟩, ⟨.hall 10 3, 356265⟩, ⟨.hall 11 3, 978120⟩, ⟨.hall 8 5, 289016⟩, ⟨.hall 6 7, 1328600⟩, ⟨.hall 4 12, 78043680⟩]
  caps := #[0, 0, 73873800, 4324320, 0, 478800, 1247400, 0, 0, 81536, 0, 25200, 0, 0, 0, 0, 0, 0] }

theorem case_35_18_10_checked :
    (Witness.linear .positive case_35_18_10).check 35 18 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_18_11 : Certificate := {
  objectiveScale := 2866500000
  eta := 7661700446400
  rows := #[⟨.count 2, 1980354776400⟩, ⟨.count 3, 525930284880⟩, ⟨.count 4, 163560917520⟩, ⟨.count 5, 54583729200⟩, ⟨.count 6, 19859439600⟩, ⟨.count 7, 8059451400⟩, ⟨.count 8, 3723239520⟩, ⟨.count 9, 2936213280⟩, ⟨.count 10, 2232430200⟩, ⟨.count 12, 2854051200⟩, ⟨.path 9, 701003160⟩, ⟨.privateRow 3 15, 39318519240⟩, ⟨.privateRow 11 0, 191891700⟩, ⟨.hall 9 2, 71351280⟩, ⟨.hall 9 3, 53813760⟩, ⟨.hall 8 4, 100228128⟩, ⟨.hall 7 5, 64387050⟩, ⟨.hall 8 6, 8252244⟩, ⟨.hall 6 7, 151381230⟩, ⟨.hall 7 7, 100413495⟩, ⟨.hall 5 9, 337795920⟩, ⟨.hall 4 11, 1154361780⟩, ⟨.hall 3 14, 77049868896⟩, ⟨.assumptionRow 11, 2243641400⟩]
  caps := #[0, 16382860000, 274760200, 0, 32104800, 6606600, 20896200, 10991760, 16765320, 8431280, 23951200, 0, 12448800, 0, 0, 0, 0, 0] }

theorem case_35_18_11_checked :
    (Witness.linear .conditional case_35_18_11).check 35 18 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_19_1_checked :
    (Witness.rising).check 35 19 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_19_2_checked :
    (Witness.rising).check 35 19 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_19_3_checked :
    (Witness.rising).check 35 19 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_19_4_checked :
    (Witness.rising).check 35 19 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_19_5_checked :
    (Witness.rising).check 35 19 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_19_6_checked :
    (Witness.rising).check 35 19 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_19_7_checked :
    (Witness.rising).check 35 19 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_19_8 : Certificate := {
  objectiveScale := 27096759360000
  eta := 88352879052438000
  rows := #[⟨.count 2, 17090906127815520⟩, ⟨.count 3, 2372104507893120⟩, ⟨.count 4, 429050087706240⟩, ⟨.count 5, 102741879240000⟩, ⟨.count 6, 35305845775200⟩, ⟨.count 7, 27067815094320⟩, ⟨.path 8, 8041659225600⟩, ⟨.path 9, 4382284991040⟩, ⟨.privateRow 5 8, 146774113200⟩, ⟨.privateRow 5 9, 5959028995920⟩, ⟨.privateRow 5 10, 6164512754400⟩, ⟨.privateRow 5 11, 5034352082760⟩, ⟨.privateRow 6 5, 1017040824800⟩, ⟨.privateRow 6 6, 2253316215150⟩, ⟨.privateRow 6 7, 3042227073600⟩, ⟨.privateRow 6 8, 1307623917600⟩, ⟨.privateRow 7 2, 662303023200⟩, ⟨.privateRow 7 3, 1429046138520⟩, ⟨.privateRow 8 0, 722825443340⟩, ⟨.privateRow 9 0, 400212168720⟩, ⟨.hall 4 13, 927612395424⟩, ⟨.hall 3 14, 4975275502197⟩]
  caps := #[0, 21881667384720, 0, 0, 662850254880, 0, 0, 181232429760, 37241157140, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_35_19_8_checked :
    (Witness.linear .positive case_35_19_8).check 35 19 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_19_9 : Certificate := {
  objectiveScale := 1742400000
  eta := 7174727960400
  rows := #[⟨.count 2, 1406809404000⟩, ⟨.count 3, 256935959280⟩, ⟨.count 4, 54226972800⟩, ⟨.count 5, 13794580800⟩, ⟨.count 6, 4410806400⟩, ⟨.count 7, 1861619760⟩, ⟨.count 8, 1735493760⟩, ⟨.path 9, 103878720⟩, ⟨.path 10, 481681728⟩, ⟨.privateRow 5 10, 1127350224⟩, ⟨.privateRow 5 11, 1349728380⟩, ⟨.privateRow 6 7, 353667600⟩, ⟨.privateRow 6 8, 589188600⟩, ⟨.privateRow 6 9, 758918160⟩, ⟨.privateRow 6 10, 648648000⟩, ⟨.privateRow 7 4, 93693600⟩, ⟨.privateRow 7 5, 191351160⟩, ⟨.privateRow 7 6, 472586400⟩, ⟨.privateRow 8 2, 148324176⟩, ⟨.privateRow 8 3, 61101040⟩, ⟨.privateRow 9 0, 72006480⟩, ⟨.privateRow 10 0, 47999952⟩, ⟨.hall 4 11, 21483792⟩, ⟨.hall 5 13, 237837600⟩, ⟨.hall 3 14, 1070566497⟩]
  caps := #[0, 0, 890192160, 396169488, 0, 0, 28468440, 0, 13004992, 0, 1682208, 0, 0, 0, 0, 0, 0] }

theorem case_35_19_9_checked :
    (Witness.linear .positive case_35_19_9).check 35 19 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_19_10 : Certificate := {
  objectiveScale := 198000000
  eta := 1201198798800
  rows := #[⟨.count 2, 282804762240⟩, ⟨.count 3, 63692909280⟩, ⟨.count 4, 16315659360⟩, ⟨.count 5, 4162158000⟩, ⟨.count 6, 1286485200⟩, ⟨.count 7, 446486040⟩, ⟨.count 8, 195074880⟩, ⟨.count 9, 196756560⟩, ⟨.path 11, 49500000⟩, ⟨.privateRow 10 2, 5810805⟩, ⟨.privateRow 11 0, 5405400⟩, ⟨.hall 11 2, 3539250⟩, ⟨.hall 9 3, 198198⟩, ⟨.hall 8 4, 198016⟩, ⟨.hall 12 4, 8154432⟩, ⟨.hall 7 5, 2085720⟩, ⟨.hall 10 8, 4804800⟩, ⟨.hall 8 9, 19752096⟩, ⟨.hall 6 10, 11100600⟩]
  caps := #[0, 2146201200, 335237760, 13590720, 19340640, 0, 514800, 0, 2925120, 1243440, 3581325, 11061600, 0, 0, 0, 0, 0] }

theorem case_35_19_10_checked :
    (Witness.linear .positive case_35_19_10).check 35 19 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_19_11 : Certificate := {
  objectiveScale := 8568000000
  eta := 34401900733200
  rows := #[⟨.count 2, 8928550350720⟩, ⟨.count 3, 2449394307360⟩, ⟨.count 4, 703523620800⟩, ⟨.count 5, 216313297200⟩, ⟨.count 6, 76453977600⟩, ⟨.count 7, 29589159600⟩, ⟨.count 8, 14637342720⟩, ⟨.count 9, 10549178640⟩, ⟨.count 10, 8454045600⟩, ⟨.count 12, 8086478400⟩, ⟨.path 9, 2192477760⟩, ⟨.privateRow 5 11, 33963209280⟩, ⟨.privateRow 6 9, 15976920960⟩, ⟨.privateRow 6 10, 37108971900⟩, ⟨.privateRow 7 6, 241544160⟩, ⟨.privateRow 7 7, 7149182040⟩, ⟨.privateRow 7 8, 18165171024⟩, ⟨.privateRow 7 9, 24516732240⟩, ⟨.privateRow 8 4, 50029980⟩, ⟨.privateRow 8 5, 3651167520⟩, ⟨.privateRow 8 6, 9172163000⟩, ⟨.privateRow 8 7, 13385163792⟩, ⟨.privateRow 9 3, 1911859950⟩, ⟨.privateRow 9 4, 5288883600⟩, ⟨.privateRow 9 5, 1629547920⟩, ⟨.privateRow 10 1, 1225224000⟩, ⟨.privateRow 10 2, 1240539300⟩, ⟨.privateRow 11 0, 578578000⟩, ⟨.hall 6 11, 351073800⟩, ⟨.hall 5 12, 17098606800⟩, ⟨.hall 6 12, 46709308800⟩, ⟨.hall 4 13, 33716764224⟩, ⟨.hall 3 14, 43779857121⟩, ⟨.hall 2 16, 467493586560⟩, ⟨.assumptionRow 11, 8366009400⟩]
  caps := #[0, 0, 532097280, 1019561400, 1056755700, 105557760, 0, 102390660, 165691724, 17876520, 0, 116548600, 481521600, 0, 0, 0, 0] }

theorem case_35_19_11_checked :
    (Witness.linear .conditional case_35_19_11).check 35 19 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_19_12 : Certificate := {
  objectiveScale := 146568834720000
  eta := 507818690553774600
  rows := #[⟨.count 2, 132875250486058080⟩, ⟨.count 3, 35761879616463000⟩, ⟨.count 4, 10081444158545760⟩, ⟨.count 5, 3030371728183800⟩, ⟨.count 6, 957460912808400⟩, ⟨.count 7, 323440776018360⟩, ⟨.count 8, 103738164129600⟩, ⟨.count 9, 50016614848200⟩, ⟨.count 10, 47634871284000⟩, ⟨.count 11, 52398358412400⟩, ⟨.count 13, 136235731872240⟩, ⟨.path 8, 54919767302400⟩, ⟨.privateRow 2 17, 7947084359214000⟩, ⟨.privateRow 5 11, 722224040117580⟩, ⟨.privateRow 6 8, 2249424477300⟩, ⟨.privateRow 6 9, 270883634701680⟩, ⟨.privateRow 6 10, 772677307952550⟩, ⟨.privateRow 7 7, 99398098079280⟩, ⟨.privateRow 7 8, 334587335898816⟩, ⟨.privateRow 7 9, 562686917042250⟩, ⟨.privateRow 8 5, 31862436125520⟩, ⟨.privateRow 8 6, 147641637163020⟩, ⟨.privateRow 8 7, 294468188750736⟩, ⟨.privateRow 8 8, 364565548226880⟩, ⟨.privateRow 9 3, 6113141814780⟩, ⟨.privateRow 9 4, 64518786772440⟩, ⟨.privateRow 9 5, 159620925163700⟩, ⟨.privateRow 9 6, 112926401523936⟩, ⟨.privateRow 10 2, 20899799775855⟩, ⟨.privateRow 10 3, 92479700107080⟩, ⟨.privateRow 10 4, 6748273431900⟩, ⟨.privateRow 11 1, 37611700451325⟩, ⟨.privateRow 12 0, 9824692202325⟩, ⟨.hall 6 9, 1487340561420⟩, ⟨.hall 6 10, 32478321330000⟩, ⟨.hall 5 11, 16962289101450⟩, ⟨.hall 7 11, 120317745718170⟩, ⟨.hall 5 12, 387229626729000⟩, ⟨.hall 4 13, 851148953411328⟩, ⟨.hall 3 14, 1144947796609617⟩, ⟨.hall 2 16, 15277100991712560⟩, ⟨.assumptionRow 12, 48911796738000⟩]
  caps := #[0, 0, 0, 19378540981800, 1770905075940, 6696531201360, 0, 236412725640, 2277534634452, 0, 3102869369115, 0, 0, 10333102847760, 0, 0, 0] }

theorem case_35_19_12_checked :
    (Witness.linear .conditional case_35_19_12).check 35 19 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_20_1_checked :
    (Witness.rising).check 35 20 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_20_2_checked :
    (Witness.rising).check 35 20 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_20_3_checked :
    (Witness.rising).check 35 20 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_20_4_checked :
    (Witness.rising).check 35 20 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_20_5_checked :
    (Witness.rising).check 35 20 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_20_6_checked :
    (Witness.rising).check 35 20 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_20_7_checked :
    (Witness.rising).check 35 20 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_20_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_35_20_8_checked :
    (Witness.linear .positive case_35_20_8).check 35 20 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_20_9 : Certificate := {
  objectiveScale := 11107800000
  eta := 82159833515760
  rows := #[⟨.count 2, 15269292838800⟩, ⟨.count 3, 2971780812000⟩, ⟨.count 4, 616998301920⟩, ⟨.count 5, 142799857200⟩, ⟨.count 6, 38594556000⟩, ⟨.count 7, 14408634240⟩, ⟨.count 8, 11406835440⟩, ⟨.path 9, 3245606595⟩, ⟨.path 10, 1262098530⟩, ⟨.privateRow 3 17, 308499150960⟩, ⟨.privateRow 6 9, 14237102880⟩, ⟨.privateRow 8 12, 10131070950⟩, ⟨.privateRow 9 3, 133413280⟩, ⟨.privateRow 10 0, 116953200⟩, ⟨.hall 8 3, 8186724⟩, ⟨.hall 9 3, 8576568⟩, ⟨.hall 3 14, 3437942508⟩]
  caps := #[0, 0, 0, 0, 0, 0, 172002600, 0, 0, 437587735, 0, 0, 0, 0, 0, 0] }

theorem case_35_20_9_checked :
    (Witness.linear .positive case_35_20_9).check 35 20 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_20_10 : Certificate := {
  objectiveScale := 1815000
  eta := 15270495240
  rows := #[⟨.count 2, 3778975200⟩, ⟨.count 3, 919638720⟩, ⟨.count 4, 228588360⟩, ⟨.count 5, 62462400⟩, ⟨.count 6, 17297280⟩, ⟨.count 7, 5605600⟩, ⟨.count 8, 2242240⟩, ⟨.count 9, 1801800⟩, ⟨.path 10, 495000⟩, ⟨.hall 8 9, 102557⟩]
  caps := #[0, 0, 0, 566280, 101640, 0, 27720, 4400, 105380, 13200, 0, 0, 0, 0, 0, 0] }

theorem case_35_20_10_checked :
    (Witness.linear .positive case_35_20_10).check 35 20 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_20_11 : Certificate := {
  objectiveScale := 67387075200000
  eta := 612198711753108480
  rows := #[⟨.count 2, 144368288643458880⟩, ⟨.count 3, 35096556721786560⟩, ⟨.count 4, 9547054894016640⟩, ⟨.count 5, 2709420901387200⟩, ⟨.count 6, 829689885984960⟩, ⟨.count 7, 288555199732800⟩, ⟨.count 8, 125914996247040⟩, ⟨.count 9, 80945354730240⟩, ⟨.count 10, 56212051896000⟩, ⟨.count 12, 74199908502720⟩, ⟨.path 8, 20910015846720⟩, ⟨.path 9, 9144753680700⟩, ⟨.privateRow 4 13, 182408108402520⟩, ⟨.privateRow 4 14, 1541709210000960⟩, ⟨.privateRow 5 11, 236990010793536⟩, ⟨.privateRow 5 12, 659367368740080⟩, ⟨.privateRow 5 13, 1255402492344000⟩, ⟨.privateRow 6 9, 154583142714000⟩, ⟨.privateRow 6 10, 323106874298208⟩, ⟨.privateRow 6 11, 569709145965960⟩, ⟨.privateRow 6 12, 607090160476800⟩, ⟨.privateRow 7 7, 84371613131520⟩, ⟨.privateRow 7 8, 106303235918880⟩, ⟨.privateRow 7 9, 420166350571968⟩, ⟨.privateRow 7 10, 112986224310960⟩, ⟨.privateRow 8 5, 44348966777115⟩, ⟨.privateRow 8 6, 96778416014280⟩, ⟨.privateRow 8 7, 117936007769580⟩, ⟨.privateRow 9 3, 24316917264640⟩, ⟨.privateRow 9 4, 56774172414960⟩, ⟨.privateRow 10 1, 15289678115712⟩, ⟨.privateRow 10 2, 6120867873120⟩, ⟨.privateRow 11 0, 4721812359264⟩, ⟨.hall 4 14, 7935267992652⟩, ⟨.hall 5 14, 317035972693440⟩, ⟨.hall 4 15, 2422317846328380⟩, ⟨.hall 3 16, 6114945400724160⟩, ⟨.hall 2 17, 8020460480192160⟩, ⟨.assumptionRow 11, 72328794048000⟩]
  caps := #[0, 863005337555400, 0, 0, 14531410487880, 2489133921480, 0, 6356745488808, 3453093738105, 562269228092, 827064036288, 0, 0, 0, 0, 0] }

theorem case_35_20_11_checked :
    (Witness.linear .conditional case_35_20_11).check 35 20 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_20_12 : Certificate := {
  objectiveScale := 16474074400000
  eta := 167967544016432160
  rows := #[⟨.count 2, 36122983937520480⟩, ⟨.count 3, 8745880173030000⟩, ⟨.count 4, 2109006533153520⟩, ⟨.count 5, 510365648192400⟩, ⟨.count 6, 125395476766560⟩, ⟨.count 7, 31803200629200⟩, ⟨.count 8, 8480853501120⟩, ⟨.count 9, 7269303000960⟩, ⟨.count 10, 7572190626000⟩, ⟨.count 11, 6663527750880⟩, ⟨.path 7, 15505384314420⟩, ⟨.privateRow 2 18, 1689204284848080⟩, ⟨.privateRow 4 13, 120359970000270⟩, ⟨.privateRow 4 14, 488103407751960⟩, ⟨.privateRow 5 11, 81355616085744⟩, ⟨.privateRow 5 12, 204070537370700⟩, ⟨.privateRow 5 13, 413037758012880⟩, ⟨.privateRow 6 9, 38542450286340⟩, ⟨.privateRow 6 10, 92047549249656⟩, ⟨.privateRow 6 11, 183966371258670⟩, ⟨.privateRow 6 12, 231456626801400⟩, ⟨.privateRow 7 7, 15331883115120⟩, ⟨.privateRow 7 8, 42757636401480⟩, ⟨.privateRow 7 9, 89614351995168⟩, ⟨.privateRow 7 10, 120322109047140⟩, ⟨.privateRow 7 11, 43447547102960⟩, ⟨.privateRow 8 5, 4991335654305⟩, ⟨.privateRow 8 6, 19877000393250⟩, ⟨.privateRow 8 7, 47528116495860⟩, ⟨.privateRow 8 8, 51450511240128⟩, ⟨.privateRow 9 3, 706737791760⟩, ⟨.privateRow 9 4, 8985666209520⟩, ⟨.privateRow 9 5, 26942575408320⟩, ⟨.privateRow 9 6, 10129908348560⟩, ⟨.privateRow 10 2, 2305311368360⟩, ⟨.privateRow 10 3, 13497429790845⟩, ⟨.privateRow 11 1, 4610622736720⟩, ⟨.privateRow 12 0, 1110587958480⟩, ⟨.hall 5 14, 283401854495760⟩, ⟨.hall 4 15, 1050546796974675⟩, ⟨.hall 3 16, 2283630157448640⟩, ⟨.hall 2 17, 3409690130526680⟩, ⟨.assumptionRow 12, 8263294857360⟩]
  caps := #[0, 115873180902960, 0, 1628286619960, 677346190180, 0, 0, 305461897300, 278492966961, 287254064640, 1198356531645, 1665865127440, 0, 16474074400000, 0, 0] }

theorem case_35_20_12_checked :
    (Witness.linear .conditional case_35_20_12).check 35 20 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_21_1_checked :
    (Witness.rising).check 35 21 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_21_2_checked :
    (Witness.rising).check 35 21 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_21_3_checked :
    (Witness.rising).check 35 21 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_21_4_checked :
    (Witness.rising).check 35 21 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_21_5_checked :
    (Witness.rising).check 35 21 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_21_6_checked :
    (Witness.rising).check 35 21 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_21_7_checked :
    (Witness.rising).check 35 21 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_21_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_35_21_8_checked :
    (Witness.linear .positive case_35_21_8).check 35 21 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_21_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_35_21_9_checked :
    (Witness.linear .positive case_35_21_9).check 35 21 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_21_10 : Certificate := {
  objectiveScale := 19800000
  eta := 309240411480
  rows := #[⟨.count 2, 68735066400⟩, ⟨.count 3, 16981604640⟩, ⟨.count 4, 4104500400⟩, ⟨.count 5, 1072071000⟩, ⟨.count 6, 298137840⟩, ⟨.count 7, 89339250⟩, ⟨.count 8, 36756720⟩, ⟨.count 9, 30630600⟩, ⟨.path 9, 8485125⟩, ⟨.hall 8 4, 531216⟩, ⟨.hall 7 6, 77690⟩, ⟨.hall 10 6, 6630⟩]
  caps := #[0, 0, 20763600, 5025735, 2118600, 0, 0, 1171500, 13530, 0, 0, 0, 0, 0, 0] }

theorem case_35_21_10_checked :
    (Witness.linear .positive case_35_21_10).check 35 21 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_21_11 : Certificate := {
  objectiveScale := 20349000000
  eta := 382494471559200
  rows := #[⟨.count 2, 78972548054400⟩, ⟨.count 3, 18513992296800⟩, ⟨.count 4, 4497552259200⟩, ⟨.count 5, 1222160940000⟩, ⟨.count 6, 344532988800⟩, ⟨.count 7, 109994484600⟩, ⟨.count 8, 41902660800⟩, ⟨.count 9, 20951330400⟩, ⟨.count 10, 13967553600⟩, ⟨.path 8, 14372658300⟩, ⟨.privateRow 2 19, 460929268800⟩, ⟨.privateRow 3 17, 1965351187800⟩, ⟨.privateRow 4 14, 404186082300⟩, ⟨.privateRow 4 15, 874136062800⟩, ⟨.privateRow 4 16, 1325171647800⟩, ⟨.privateRow 5 11, 31426995600⟩, ⟨.privateRow 5 12, 272087944128⟩, ⟨.privateRow 5 13, 416931474960⟩, ⟨.privateRow 5 14, 623884060800⟩, ⟨.privateRow 5 15, 446961715200⟩, ⟨.privateRow 6 9, 44452293600⟩, ⟨.privateRow 6 10, 132821088400⟩, ⟨.privateRow 6 11, 215255520480⟩, ⟨.privateRow 6 12, 300884383800⟩, ⟨.privateRow 6 13, 61819357600⟩, ⟨.privateRow 7 7, 34118659575⟩, ⟨.privateRow 7 8, 72664534800⟩, ⟨.privateRow 7 9, 111352441200⟩, ⟨.privateRow 7 10, 68324616360⟩, ⟨.privateRow 8 5, 22244622400⟩, ⟨.privateRow 8 6, 46704007350⟩, ⟨.privateRow 8 7, 27436266000⟩, ⟨.privateRow 9 3, 14200346160⟩, ⟨.privateRow 9 4, 14743528800⟩, ⟨.privateRow 10 1, 7364710080⟩, ⟨.privateRow 11 0, 1904666400⟩, ⟨.privateRow 12 0, 2560718160⟩, ⟨.hall 4 16, 73124251200⟩, ⟨.hall 3 17, 862108447200⟩, ⟨.hall 2 18, 1989273686400⟩, ⟨.assumptionRow 11, 23547223260⟩]
  caps := #[0, 385114476240, 0, 28399817160, 0, 726677952, 2067961140, 1593438990, 133975270, 5597680440, 0, 24997351140, 0, 0, 0] }

theorem case_35_21_11_checked :
    (Witness.linear .conditional case_35_21_11).check 35 21 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_21_12 : Certificate := {
  objectiveScale := 10451246400000
  eta := 142335880063977600
  rows := #[⟨.count 2, 32156269508563200⟩, ⟨.count 3, 7077338457789600⟩, ⟨.count 4, 1739630865772800⟩, ⟨.count 5, 430424131737600⟩, ⟨.count 6, 107606032934400⟩, ⟨.count 7, 27461956321800⟩, ⟨.count 8, 7472641176000⟩, ⟨.count 9, 4483584705600⟩, ⟨.count 10, 4483584705600⟩, ⟨.path 7, 10765771288272⟩, ⟨.privateRow 2 19, 3871575393285600⟩, ⟨.privateRow 3 16, 550733654671200⟩, ⟨.privateRow 3 17, 1403548828882200⟩, ⟨.privateRow 4 14, 381384924020100⟩, ⟨.privateRow 4 15, 632185443489600⟩, ⟨.privateRow 4 16, 961728919351200⟩, ⟨.privateRow 5 11, 24061904586720⟩, ⟨.privateRow 5 12, 164278543613184⟩, ⟨.privateRow 5 13, 290536288922880⟩, ⟨.privateRow 5 14, 465545545264800⟩, ⟨.privateRow 5 15, 389175152446080⟩, ⟨.privateRow 6 9, 18788354956800⟩, ⟨.privateRow 6 10, 71156149864800⟩, ⟨.privateRow 6 11, 133859912266080⟩, ⟨.privateRow 6 12, 227043747730800⟩, ⟨.privateRow 6 13, 190552349988000⟩, ⟨.privateRow 7 7, 9807841543500⟩, ⟨.privateRow 7 8, 34240709388600⟩, ⟨.privateRow 7 9, 65696970339000⟩, ⟨.privateRow 7 10, 119151263551320⟩, ⟨.privateRow 7 11, 34420853416950⟩, ⟨.privateRow 8 5, 3943893954000⟩, ⟨.privateRow 8 6, 17957690826075⟩, ⟨.privateRow 8 7, 36749381783400⟩, ⟨.privateRow 8 8, 42936550757100⟩, ⟨.privateRow 9 3, 797081725440⟩, ⟨.privateRow 9 4, 9769786426400⟩, ⟨.privateRow 9 5, 23694499728900⟩, ⟨.privateRow 9 6, 1316608207200⟩, ⟨.privateRow 10 2, 3990390387984⟩, ⟨.privateRow 10 3, 7572276391680⟩, ⟨.privateRow 11 0, 611397914400⟩, ⟨.privateRow 11 1, 2578061205720⟩, ⟨.privateRow 12 0, 821990529360⟩, ⟨.hall 4 16, 161145309124800⟩, ⟨.hall 3 17, 758971255442400⟩, ⟨.hall 2 18, 1728775871222400⟩, ⟨.assumptionRow 12, 6757384000500⟩]
  caps := #[0, 0, 17424472324896, 4477280928120, 4573223534880, 0, 0, 0, 0, 1827451583320, 1372666702176, 3965594805900, 0, 10451246400000, 0] }

theorem case_35_21_12_checked :
    (Witness.linear .conditional case_35_21_12).check 35 21 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_21_13 : Certificate := {
  objectiveScale := 46108440000000
  eta := 686033295803856000
  rows := #[⟨.count 2, 163247319130896000⟩, ⟨.count 3, 38530806063750000⟩, ⟨.count 4, 9168930722952000⟩, ⟨.count 5, 2331464046912000⟩, ⟨.count 6, 575393370552000⟩, ⟨.count 7, 130771220580000⟩, ⟨.count 8, 22417923528000⟩, ⟨.path 7, 25461903523056⟩, ⟨.path 8, 21182949216000⟩, ⟨.privateRow 2 19, 22317042872124000⟩, ⟨.privateRow 3 16, 2411172219456000⟩, ⟨.privateRow 3 17, 7911658845090000⟩, ⟨.privateRow 4 14, 1644915138867000⟩, ⟨.privateRow 4 15, 3502800551250000⟩, ⟨.privateRow 4 16, 5842671319485000⟩, ⟨.privateRow 5 11, 17560706763600⟩, ⟨.privateRow 5 12, 780592097244960⟩, ⟨.privateRow 5 13, 1528341936521400⟩, ⟨.privateRow 5 14, 2830636477468800⟩, ⟨.privateRow 5 15, 2759646386296800⟩, ⟨.privateRow 6 9, 32025605040000⟩, ⟨.privateRow 6 10, 312605489196000⟩, ⟨.privateRow 6 11, 694955629368000⟩, ⟨.privateRow 6 12, 1091628331794000⟩, ⟨.privateRow 6 13, 2059127790720000⟩, ⟨.privateRow 6 14, 291433005864000⟩, ⟨.privateRow 7 7, 20900043289125⟩, ⟨.privateRow 7 8, 129169940328000⟩, ⟨.privateRow 7 9, 315096369588000⟩, ⟨.privateRow 7 10, 673845418045800⟩, ⟨.privateRow 7 11, 785094363553500⟩, ⟨.privateRow 8 5, 9548374836000⟩, ⟨.privateRow 8 6, 56745368930250⟩, ⟨.privateRow 8 7, 147851543268000⟩, ⟨.privateRow 8 8, 369428698138500⟩, ⟨.privateRow 8 9, 235388197044000⟩, ⟨.privateRow 9 3, 3113600490000⟩, ⟨.privateRow 9 4, 25047186164000⟩, ⟨.privateRow 9 5, 79708172544000⟩, ⟨.privateRow 9 6, 211013153208000⟩, ⟨.privateRow 10 1, 1222795828800⟩, ⟨.privateRow 10 2, 8742990175920⟩, ⟨.privateRow 10 3, 44337670977600⟩, ⟨.privateRow 10 4, 65011978231200⟩, ⟨.privateRow 11 0, 5604480882000⟩, ⟨.privateRow 11 1, 16813442646000⟩, ⟨.privateRow 11 2, 16813442646000⟩, ⟨.privateRow 12 0, 12329857940400⟩, ⟨.hall 4 16, 1591672570488000⟩, ⟨.hall 3 17, 5161415532273000⟩, ⟨.hall 2 18, 10512826243920000⟩]
  caps := #[0, 0, 119027659540608, 0, 607510984080, 7798167336960, 5730970442472, 845231029806, 0, 3477983212000, 5995111585680, 28190700216000, 0, 322759080000000, 46108440000000] }

theorem case_35_21_13_checked :
    (Witness.linear .negative case_35_21_13).check 35 21 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_22_1_checked :
    (Witness.rising).check 35 22 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_22_2_checked :
    (Witness.rising).check 35 22 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_22_3_checked :
    (Witness.rising).check 35 22 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_22_4_checked :
    (Witness.rising).check 35 22 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_22_5_checked :
    (Witness.rising).check 35 22 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_22_6_checked :
    (Witness.rising).check 35 22 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_22_7_checked :
    (Witness.rising).check 35 22 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_22_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_35_22_8_checked :
    (Witness.linear .positive case_35_22_8).check 35 22 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_22_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_35_22_9_checked :
    (Witness.linear .positive case_35_22_9).check 35 22 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_22_10 : Certificate := {
  objectiveScale := 1
  eta := 3718
  rows := #[⟨.assumptionRow 10, 4⟩]
  caps := #[0, 0, 1144, 363, 120, 42, 16, 7, 4, 17, 7, 1, 0, 0] }

theorem case_35_22_10_checked :
    (Witness.linear .conditional case_35_22_10).check 35 22 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_22_11 : Certificate := {
  objectiveScale := 254239408500000
  eta := 7280205259506379200
  rows := #[⟨.count 2, 1415101022324589600⟩, ⟨.count 3, 303409310103900000⟩, ⟨.count 4, 68610958658161920⟩, ⟨.count 5, 16181829872208000⟩, ⟨.count 6, 4045457468052000⟩, ⟨.count 7, 1078788658147200⟩, ⟨.count 8, 359596219382400⟩, ⟨.count 9, 323636597444160⟩, ⟨.path 7, 388486552053600⟩, ⟨.path 8, 19969836486600⟩, ⟨.privateRow 2 20, 132016762040763600⟩, ⟨.privateRow 3 17, 37847502089997600⟩, ⟨.privateRow 3 18, 49354581110234400⟩, ⟨.privateRow 4 14, 7686369189298800⟩, ⟨.privateRow 4 15, 18770922651761280⟩, ⟨.privateRow 4 16, 22735470970452240⟩, ⟨.privateRow 4 17, 25769564071491240⟩, ⟨.privateRow 5 11, 986321058877440⟩, ⟨.privateRow 5 12, 5531788508165920⟩, ⟨.privateRow 5 13, 8486470777424640⟩, ⟨.privateRow 5 14, 10464249984027840⟩, ⟨.privateRow 5 15, 9900882573662080⟩, ⟨.privateRow 6 9, 1177115749384575⟩, ⟨.privateRow 6 10, 3014829017857800⟩, ⟨.privateRow 6 11, 4423782657193900⟩, ⟨.privateRow 6 12, 4697225615682600⟩, ⟨.privateRow 7 6, 38528166362400⟩, ⟨.privateRow 7 7, 898990548456000⟩, ⟨.privateRow 7 8, 1798783767044550⟩, ⟨.privateRow 7 9, 1926408318120000⟩, ⟨.privateRow 8 4, 49035848097600⟩, ⟨.privateRow 8 5, 647273194888320⟩, ⟨.privateRow 8 6, 786616729899000⟩, ⟨.privateRow 9 2, 29966351615200⟩, ⟨.privateRow 9 3, 385748671701120⟩, ⟨.privateRow 10 1, 101136436701300⟩, ⟨.privateRow 11 0, 22474763711400⟩, ⟨.hall 3 18, 6983737102742400⟩, ⟨.hall 2 19, 39605028612229080⟩, ⟨.assumptionRow 11, 301230986851872⟩]
  caps := #[0, 0, 0, 179786598879888, 0, 0, 188321275747319, 39030791908416, 36041095328784, 0, 0, 0, 254239408500000, 0] }

theorem case_35_22_11_checked :
    (Witness.linear .conditional case_35_22_11).check 35 22 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_22_12 : Certificate := {
  objectiveScale := 73743847128000000
  eta := 3081028139156282515200
  rows := #[⟨.count 2, 520603833037159872000⟩, ⟨.count 3, 95515744573759910400⟩, ⟨.count 4, 17812395609701172480⟩, ⟨.count 5, 3406154554995192000⟩, ⟨.count 6, 645376652525404800⟩, ⟨.count 7, 134453469276126000⟩, ⟨.count 8, 71708516947267200⟩, ⟨.path 3, 2627734432122399600⟩, ⟨.path 6, 306644719300920000⟩, ⟨.privateRow 2 20, 52060383303715987200⟩, ⟨.privateRow 3 17, 13391565539902149600⟩, ⟨.privateRow 3 18, 19011720555644216400⟩, ⟨.privateRow 4 14, 2229776334475273584⟩, ⟨.privateRow 4 15, 6437632108940912880⟩, ⟨.privateRow 4 16, 8750231780490280080⟩, ⟨.privateRow 4 17, 11213419337628908400⟩, ⟨.privateRow 5 11, 170051625903519360⟩, ⟨.privateRow 5 12, 1542928256315365920⟩, ⟨.privateRow 5 13, 2818144716027600960⟩, ⟨.privateRow 5 14, 2463187557138628320⟩, ⟨.privateRow 5 15, 8607412317570306240⟩, ⟨.privateRow 5 16, 103977349573537440⟩, ⟨.privateRow 6 9, 178711069579517475⟩, ⟨.privateRow 6 10, 793915723344744000⟩, ⟨.privateRow 6 11, 1414002318553925100⟩, ⟨.privateRow 6 12, 1964813364355121280⟩, ⟨.privateRow 6 13, 2058258525502028850⟩, ⟨.privateRow 7 7, 113965321576906800⟩, ⟨.privateRow 7 8, 425449192066598700⟩, ⟨.privateRow 7 9, 800135339610578400⟩, ⟨.privateRow 7 10, 1108920994220239200⟩, ⟨.privateRow 8 5, 60055882943336280⟩, ⟨.privateRow 8 6, 260441349745977400⟩, ⟨.privateRow 8 7, 524368530176891400⟩, ⟨.privateRow 8 8, 46738586938843800⟩, ⟨.privateRow 9 3, 28683406778906880⟩, ⟨.privateRow 9 4, 182139633046058688⟩, ⟨.privateRow 9 5, 90830788133205120⟩, ⟨.privateRow 10 1, 8067208156567560⟩, ⟨.privateRow 10 2, 82138846685051520⟩, ⟨.privateRow 11 0, 22408911546021000⟩, ⟨.hall 3 18, 4483669375439654400⟩, ⟨.hall 2 19, 16860465047226200400⟩, ⟨.assumptionRow 12, 55053929972452950⟩]
  caps := #[0, 762568042233324600, 50791124011446000, 154838282103905400, 78322989700968012, 5152684934829600, 19353999322783125, 26828820510020100, 0, 9940768917983904, 0, 0, 608640694179547050, 73743847128000000] }

theorem case_35_22_12_checked :
    (Witness.linear .conditional case_35_22_12).check 35 22 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_22_13 : Certificate := {
  objectiveScale := 1229905420821000000
  eta := 69396776770779108050400
  rows := #[⟨.count 2, 11634299183575279411200⟩, ⟨.count 3, 2003776670466623052000⟩, ⟨.count 4, 328867263853903494720⟩, ⟨.count 5, 45905536551354480000⟩, ⟨.count 6, 4475789813757061800⟩, ⟨.path 5, 10735760618902519200⟩, ⟨.path 6, 4384698410356664400⟩, ⟨.privateRow 2 20, 1215693371721245016600⟩, ⟨.privateRow 3 17, 292418267832128037600⟩, ⟨.privateRow 3 18, 435528778030975629000⟩, ⟨.privateRow 4 14, 46809875621416163256⟩, ⟨.privateRow 4 15, 135977937457180889070⟩, ⟨.privateRow 4 16, 197485618243926972960⟩, ⟨.privateRow 4 17, 272575599657805063620⟩, ⟨.privateRow 5 11, 4564321919963245440⟩, ⟨.privateRow 5 12, 29333637856315512720⟩, ⟨.privateRow 5 13, 57271747401469849248⟩, ⟨.privateRow 5 14, 88368157861357374000⟩, ⟨.privateRow 5 15, 134135977803057790560⟩, ⟨.privateRow 5 16, 80472405574524403440⟩, ⟨.privateRow 6 9, 4031079928415815275⟩, ⟨.privateRow 6 10, 14156939575748069100⟩, ⟨.privateRow 6 11, 27208594060125728250⟩, ⟨.privateRow 6 12, 41774038261732576800⟩, ⟨.privateRow 6 13, 67997576016693823500⟩, ⟨.privateRow 6 14, 11438129524045824600⟩, ⟨.privateRow 7 6, 24592251723939900⟩, ⟨.privateRow 7 7, 2333531441360519400⟩, ⟨.privateRow 7 8, 7230122006838330600⟩, ⟨.privateRow 7 9, 14446191298405838400⟩, ⟨.privateRow 7 10, 22928176023953300100⟩, ⟨.privateRow 7 11, 22172374154304213840⟩, ⟨.privateRow 8 5, 1250925871024409580⟩, ⟨.privateRow 8 6, 4220759055138425800⟩, ⟨.privateRow 8 7, 8894197706824930500⟩, ⟨.privateRow 8 8, 12492863875761469200⟩, ⟨.privateRow 9 3, 709449201248205600⟩, ⟨.privateRow 9 4, 2846143266183977760⟩, ⟨.privateRow 9 5, 6355366504776409120⟩, ⟨.privateRow 10 1, 533651862409495830⟩, ⟨.privateRow 10 2, 2253544521611947200⟩, ⟨.privateRow 10 3, 640382234891394996⟩, ⟨.privateRow 11 0, 1090256493094668900⟩, ⟨.privateRow 12 0, 344291524135158600⟩, ⟨.hall 3 18, 128293894256680152000⟩, ⟨.hall 2 19, 409397051349117091260⟩, ⟨.assumptionRow 13, 213571212832504800⟩]
  caps := #[0, 0, 1478072317670020800, 0, 372421526786587278, 219689140667648400, 587689005831352425, 115202205936745200, 8039606000304060, 385008157353965600, 0, 455584299103672200, 0, 9625672153735495200] }

theorem case_35_22_13_checked :
    (Witness.linear .conditional case_35_22_13).check 35 22 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_22_14 : Certificate := {
  objectiveScale := 4568625600000
  eta := 247993216525454400
  rows := #[⟨.count 2, 47829405121898400⟩, ⟨.count 3, 8737146960141600⟩, ⟨.count 4, 1564780766028480⟩, ⟨.count 5, 242319901824000⟩, ⟨.count 6, 27260988955200⟩, ⟨.path 6, 27414894592800⟩, ⟨.privateRow 6 10, 15469529446800⟩, ⟨.privateRow 8 6, 757249693200⟩, ⟨.privateRow 9 4, 302899877280⟩, ⟨.hall 10 4, 238648388160⟩, ⟨.hall 11 4, 151449938640⟩, ⟨.hall 9 5, 95318143200⟩, ⟨.hall 8 6, 210607706880⟩, ⟨.hall 9 7, 120736314720⟩, ⟨.hall 7 8, 211759257640⟩, ⟨.hall 6 9, 245359113255⟩, ⟨.hall 4 13, 1211217702552⟩, ⟨.hall 5 14, 17419712550240⟩]
  caps := #[0, 0, 20717724165600, 0, 0, 92230195200, 811461393600, 0, 834459465840, 1909032840000, 520823318400, 0, 703568342400, 123352891200000] }

theorem case_35_22_14_checked :
    (Witness.linear .negative case_35_22_14).check 35 22 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_23_1_checked :
    (Witness.rising).check 35 23 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_23_2_checked :
    (Witness.rising).check 35 23 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_23_3_checked :
    (Witness.rising).check 35 23 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_23_4_checked :
    (Witness.rising).check 35 23 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_23_5_checked :
    (Witness.rising).check 35 23 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_23_6_checked :
    (Witness.rising).check 35 23 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_23_7_checked :
    (Witness.rising).check 35 23 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_23_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_35_23_8_checked :
    (Witness.linear .positive case_35_23_8).check 35 23 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_23_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_35_23_9_checked :
    (Witness.linear .positive case_35_23_9).check 35 23 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_23_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_35_23_10_checked :
    (Witness.linear .positive case_35_23_10).check 35 23 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_23_11 : Certificate := {
  objectiveScale := 352
  eta := 1939938
  rows := #[⟨.assumptionRow 11, 911⟩]
  caps := #[0, 0, 598026, 189475, 62172, 21366, 7826, 3147, 1470, 25949, 11948, 2961, 352] }

theorem case_35_23_11_checked :
    (Witness.linear .conditional case_35_23_11).check 35 23 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_23_12 : Certificate := {
  objectiveScale := 292398528075500000
  eta := 25149409330226904122400
  rows := #[⟨.count 2, 4032447749751666445200⟩, ⟨.count 3, 659512482436020213000⟩, ⟨.count 4, 106080314635211716800⟩, ⟨.count 5, 17098471766859783300⟩, ⟨.count 6, 2691887683412327400⟩, ⟨.count 7, 697896806810603400⟩, ⟨.path 5, 3417523765337682000⟩, ⟨.path 6, 1076133119503642200⟩, ⟨.privateRow 2 21, 337084157689521442200⟩, ⟨.privateRow 3 17, 22507172019641959650⟩, ⟨.privateRow 3 18, 101055457626175372320⟩, ⟨.privateRow 3 19, 125830794267951793020⟩, ⟨.privateRow 4 14, 4420013109800488200⟩, ⟨.privateRow 4 15, 28809180185141708352⟩, ⟨.privateRow 4 16, 48782986796061177660⟩, ⟨.privateRow 4 17, 57785855603917961520⟩, ⟨.privateRow 4 18, 63717978461808090420⟩, ⟨.privateRow 5 12, 6340890987593482320⟩, ⟨.privateRow 5 13, 16016731716303348030⟩, ⟨.privateRow 5 14, 22960804944068851860⟩, ⟨.privateRow 5 15, 27654160969870159725⟩, ⟨.privateRow 5 16, 15749204607025950060⟩, ⟨.privateRow 6 9, 348948403405301700⟩, ⟨.privateRow 6 10, 4474017029375118225⟩, ⟨.privateRow 6 11, 8737952877108269100⟩, ⟨.privateRow 6 12, 12570450817910035050⟩, ⟨.privateRow 6 13, 8614040586919447680⟩, ⟨.privateRow 7 7, 333993471830788770⟩, ⟨.privateRow 7 8, 2979908587810354200⟩, ⟨.privateRow 7 9, 5670411555336152625⟩, ⟨.privateRow 7 10, 3938131981288404900⟩, ⟨.privateRow 8 5, 253780657022037600⟩, ⟨.privateRow 8 6, 2212332877589612778⟩, ⟨.privateRow 8 7, 2054918375608998900⟩, ⟨.privateRow 9 3, 197737428596337630⟩, ⟨.privateRow 9 4, 1243525219407984240⟩, ⟨.privateRow 10 1, 193263731116782480⟩, ⟨.privateRow 10 2, 209369042043181020⟩, ⟨.privateRow 11 0, 161053109263985400⟩, ⟨.hall 3 19, 1947132091001583486⟩, ⟨.hall 2 20, 77566245099807063600⟩, ⟨.assumptionRow 12, 249928719130268640⟩]
  caps := #[0, 15342762573573995560, 1579379921179220160, 2111410894701608500, 0, 370040207507350380, 383241418586653055, 27336344385647150, 249928719130268640, 167355262878865880, 2136032805176385500, 0, 2674056561624731360] }

theorem case_35_23_12_checked :
    (Witness.linear .conditional case_35_23_12).check 35 23 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_23_13 : Certificate := {
  objectiveScale := 11037222000000
  eta := 1312751951106195600
  rows := #[⟨.count 2, 195934248346636800⟩, ⟨.count 3, 28556214645918960⟩, ⟨.count 4, 3766425223841280⟩, ⟨.count 5, 369380133322200⟩, ⟨.count 6, 16098892009200⟩, ⟨.count 7, 6260680225800⟩, ⟨.path 5, 345333060072000⟩, ⟨.privateRow 2 21, 17241913341853200⟩, ⟨.privateRow 3 17, 1089358359289200⟩, ⟨.privateRow 3 18, 4778151148330560⟩, ⟨.privateRow 3 19, 6340816932690240⟩, ⟨.privateRow 4 14, 228306138900840⟩, ⟨.privateRow 4 15, 1233103577273568⟩, ⟨.privateRow 4 16, 2246332065017040⟩, ⟨.privateRow 4 17, 2906625139498080⟩, ⟨.privateRow 4 18, 3563579184525360⟩, ⟨.privateRow 5 11, 22851482824170⟩, ⟨.privateRow 5 12, 244703158539840⟩, ⟨.privateRow 5 13, 649441228756320⟩, ⟨.privateRow 5 14, 1026751557031200⟩, ⟨.privateRow 5 15, 1376097513630840⟩, ⟨.privateRow 5 16, 1512162963871560⟩, ⟨.privateRow 6 9, 27228990188400⟩, ⟨.privateRow 6 10, 155622622755600⟩, ⟨.privateRow 6 11, 337565656256400⟩, ⟨.privateRow 6 12, 540356329012500⟩, ⟨.privateRow 6 13, 726596659348560⟩, ⟨.privateRow 6 14, 226949658185250⟩, ⟨.privateRow 7 7, 19497546988920⟩, ⟨.privateRow 7 8, 98382117834000⟩, ⟨.privateRow 7 9, 206267053867875⟩, ⟨.privateRow 7 10, 336032428446000⟩, ⟨.privateRow 7 11, 138033092597400⟩, ⟨.privateRow 8 5, 14456479794120⟩, ⟨.privateRow 8 6, 71496968178636⟩, ⟨.privateRow 8 7, 157212636781200⟩, ⟨.privateRow 8 8, 59632979150745⟩, ⟨.privateRow 9 3, 13356117815040⟩, ⟨.privateRow 9 4, 65111074348320⟩, ⟨.privateRow 9 5, 30301692292872⟩, ⟨.privateRow 10 1, 17915177261520⟩, ⟨.privateRow 10 2, 18155972654820⟩, ⟨.privateRow 11 0, 11558178878400⟩, ⟨.hall 3 19, 458657433342108⟩, ⟨.hall 2 20, 4232219832640800⟩, ⟨.assumptionRow 13, 4153851686600⟩]
  caps := #[0, 168265157337200, 0, 0, 3524354476720, 11251238118120, 0, 0, 2403256777467, 9104311191976, 0, 0, 444099251134000] }

theorem case_35_23_13_checked :
    (Witness.linear .conditional case_35_23_13).check 35 23 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_23_14 : Certificate := {
  objectiveScale := 56984735697120000
  eta := 9137662591115060402400
  rows := #[⟨.count 2, 1391008035517362662400⟩, ⟨.count 3, 203147790508183641120⟩, ⟨.count 4, 27118275921783446400⟩, ⟨.count 5, 2725120864689022800⟩, ⟨.count 6, 56971167902906400⟩, ⟨.path 5, 2098901412132782400⟩, ⟨.path 6, 75945373132543200⟩, ⟨.privateRow 5 14, 1241591652497340144⟩, ⟨.privateRow 6 15, 21810462112162666800⟩, ⟨.privateRow 7 7, 6646636255339080⟩, ⟨.privateRow 8 5, 6042396595762800⟩, ⟨.privateRow 8 6, 11963945259610344⟩, ⟨.privateRow 8 7, 45787938647891440⟩, ⟨.hall 10 4, 3346558114576320⟩, ⟨.hall 8 5, 4125651008975040⟩, ⟨.hall 9 5, 2868478383922560⟩, ⟨.hall 7 7, 2462276612773341⟩, ⟨.hall 6 8, 2495466829368360⟩, ⟨.hall 5 10, 692859740367400⟩, ⟨.hall 4 13, 8587810724132640⟩, ⟨.hall 3 16, 133208467911182664⟩, ⟨.hall 2 18, 826781580513757440⟩]
  caps := #[0, 243460094848898400, 222910619868367200, 0, 6416824727117376, 304169939528400, 22139270113131600, 79389234282037680, 0, 0, 463530121513430400, 0, 6268320926683200000] }

theorem case_35_23_14_checked :
    (Witness.linear .negative case_35_23_14).check 35 23 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_24_1_checked :
    (Witness.rising).check 35 24 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_24_2_checked :
    (Witness.rising).check 35 24 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_24_3_checked :
    (Witness.rising).check 35 24 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_24_4_checked :
    (Witness.rising).check 35 24 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_24_5_checked :
    (Witness.rising).check 35 24 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_24_6_checked :
    (Witness.rising).check 35 24 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_24_7_checked :
    (Witness.rising).check 35 24 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_24_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_35_24_8_checked :
    (Witness.linear .positive case_35_24_8).check 35 24 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_24_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_35_24_9_checked :
    (Witness.linear .positive case_35_24_9).check 35 24 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_24_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_35_24_10_checked :
    (Witness.linear .positive case_35_24_10).check 35 24 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_24_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_35_24_11_checked :
    (Witness.linear .positive case_35_24_11).check 35 24 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_24_12 : Certificate := {
  objectiveScale := 943
  eta := 5754840
  rows := #[⟨.assumptionRow 12, 1530⟩]
  caps := #[0, 0, 1818440, 587587, 195085, 66975, 23980, 9055, 474964, 322630, 139629, 42935] }

theorem case_35_24_12_checked :
    (Witness.linear .conditional case_35_24_12).check 35 24 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_24_13 : Certificate := {
  objectiveScale := 26334693000000
  eta := 7746748758540792000
  rows := #[⟨.count 2, 887625073580525280⟩, ⟨.count 3, 95115955980165120⟩, ⟨.count 4, 7369009610442480⟩, ⟨.count 5, 88463500725600⟩, ⟨.path 4, 7005548724174000⟩, ⟨.privateRow 2 21, 7709594088236040⟩, ⟨.privateRow 2 22, 66506859845506080⟩, ⟨.privateRow 3 18, 13447926501969960⟩, ⟨.privateRow 3 19, 21769884600784320⟩, ⟨.privateRow 3 20, 23902837896057120⟩, ⟨.privateRow 4 14, 692226893177820⟩, ⟨.privateRow 4 15, 2554383583451700⟩, ⟨.privateRow 4 16, 8068755901181976⟩, ⟨.privateRow 4 17, 9896301246796965⟩, ⟨.privateRow 4 18, 11115438866171640⟩, ⟨.privateRow 4 19, 6517548415958580⟩, ⟨.privateRow 5 11, 186756279309600⟩, ⟨.privateRow 5 12, 558425848330350⟩, ⟨.privateRow 5 13, 1951252073147520⟩, ⟨.privateRow 5 14, 3918933082144080⟩, ⟨.privateRow 5 15, 5026496111228592⟩, ⟨.privateRow 5 16, 4573562987513520⟩, ⟨.privateRow 6 8, 16084272859200⟩, ⟨.privateRow 6 9, 117214138461420⟩, ⟨.privateRow 6 10, 485730147502600⟩, ⟨.privateRow 6 11, 1274427307328175⟩, ⟨.privateRow 6 12, 2211587518140000⟩, ⟨.privateRow 6 13, 2395886477985000⟩, ⟨.privateRow 7 5, 680488467120⟩, ⟨.privateRow 7 6, 6634762554420⟩, ⟨.privateRow 7 7, 118219405515120⟩, ⟨.privateRow 7 8, 423740168475624⟩, ⟨.privateRow 7 9, 970149724624080⟩, ⟨.privateRow 7 10, 977521683017880⟩, ⟨.privateRow 8 4, 7145128904760⟩, ⟨.privateRow 8 5, 144490384518480⟩, ⟨.privateRow 8 6, 463026004934220⟩, ⟨.privateRow 8 7, 295689251175318⟩, ⟨.privateRow 9 2, 14743916787600⟩, ⟨.privateRow 9 3, 238170963492000⟩, ⟨.privateRow 9 4, 55043956007040⟩, ⟨.privateRow 10 0, 49539560406336⟩, ⟨.privateRow 10 1, 39808575326520⟩, ⟨.hall 2 21, 9845987630759280⟩, ⟨.assumptionRow 13, 13809491654112⟩]
  caps := #[0, 1406351875143600, 0, 36320559042768, 0, 72806865279720, 1127661130512, 30693936977928, 1447284501432, 10615620087072, 805206834359928, 4579999186482720] }

theorem case_35_24_13_checked :
    (Witness.linear .conditional case_35_24_13).check 35 24 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_24_14 : Certificate := {
  objectiveScale := 839947290494400000
  eta := 158796886803516215654400
  rows := #[⟨.count 2, 23078875899242375372160⟩, ⟨.count 3, 3263829047796151074240⟩, ⟨.count 4, 409830273777731526720⟩, ⟨.count 5, 37032856064252848800⟩, ⟨.path 4, 5756508533237061600⟩, ⟨.path 5, 37498211990998387200⟩, ⟨.privateRow 2 21, 2292333790377251340720⟩, ⟨.privateRow 3 19, 2453495293619833182720⟩, ⟨.privateRow 4 14, 529040800917897840⟩, ⟨.privateRow 4 15, 100297318507351465500⟩, ⟨.privateRow 4 16, 204174479767580706384⟩, ⟨.privateRow 4 17, 651623963163915752010⟩, ⟨.privateRow 4 18, 751766978104332830640⟩, ⟨.privateRow 5 12, 13358280223176920460⟩, ⟨.privateRow 5 15, 720130338209442539808⟩, ⟨.privateRow 5 16, 64454804245163886840⟩, ⟨.privateRow 6 8, 133596161847954000⟩, ⟨.privateRow 6 10, 13781186295515610400⟩, ⟨.privateRow 6 14, 306432188353889048880⟩, ⟨.privateRow 7 5, 27130297482969120⟩, ⟨.privateRow 7 7, 128252315374035840⟩, ⟨.privateRow 7 8, 211616320367159136⟩, ⟨.privateRow 7 9, 27823627307533886400⟩, ⟨.hall 7 3, 6353676285533577⟩, ⟨.hall 8 3, 14695577803274940⟩, ⟨.hall 8 4, 18991208238078384⟩, ⟨.hall 7 5, 18552335778795060⟩, ⟨.hall 9 5, 46861422925128480⟩, ⟨.hall 7 6, 50370589076836050⟩, ⟨.hall 8 6, 36995860204048800⟩, ⟨.hall 10 8, 24663906802699200⟩, ⟨.hall 5 9, 16401243494313000⟩, ⟨.hall 6 9, 31968775670439816⟩, ⟨.hall 4 14, 41285625855371898⟩, ⟨.hall 3 16, 142873167563563008⟩, ⟨.hall 2 20, 73424450551635518400⟩, ⟨.hall 1 22, 1970791992288934214400⟩]
  caps := #[0, 60838091680358440800, 4297775215556607840, 0, 642585081998747316, 1858496702496002712, 2055325566891600, 2830036187569155696, 69022668596377320, 3060274457528428140, 0, 96690532345262856000] }

theorem case_35_24_14_checked :
    (Witness.linear .negative case_35_24_14).check 35 24 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_24_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 1430, 1430, 1001, 572] }

theorem case_35_24_15_checked :
    (Witness.linear .negative case_35_24_15).check 35 24 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_25_1_checked :
    (Witness.rising).check 35 25 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_25_2_checked :
    (Witness.rising).check 35 25 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_25_3_checked :
    (Witness.rising).check 35 25 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_25_4_checked :
    (Witness.rising).check 35 25 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_25_5_checked :
    (Witness.rising).check 35 25 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_25_6_checked :
    (Witness.rising).check 35 25 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_25_7_checked :
    (Witness.rising).check 35 25 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_25_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_35_25_8_checked :
    (Witness.linear .positive case_35_25_8).check 35 25 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_25_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_35_25_9_checked :
    (Witness.linear .positive case_35_25_9).check 35 25 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_25_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_35_25_10_checked :
    (Witness.linear .positive case_35_25_10).check 35 25 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_25_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_35_25_11_checked :
    (Witness.linear .positive case_35_25_11).check 35 25 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_25_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_35_25_12_checked :
    (Witness.linear .positive case_35_25_12).check 35 25 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_25_13 : Certificate := {
  objectiveScale := 274
  eta := 2773278
  rows := #[⟨.assumptionRow 13, 363⟩]
  caps := #[0, 0, 871624, 277914, 90090, 32461, 12120, 4692, 313208, 240772, 122290] }

theorem case_35_25_13_checked :
    (Witness.linear .conditional case_35_25_13).check 35 25 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_25_14 : Certificate := {
  objectiveScale := 11
  eta := 38760
  rows := #[⟨.assumptionRow 14, 9⟩]
  caps := #[0, 0, 13804, 4732, 2002, 781, 290, 11934, 22100, 17108, 9828] }

theorem case_35_25_14_checked :
    (Witness.linear .conditional case_35_25_14).check 35 25 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_25_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 4862, 4862, 3432, 2002] }

theorem case_35_25_15_checked :
    (Witness.linear .negative case_35_25_15).check 35 25 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_25_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 1430, 1430] }

theorem case_35_25_16_checked :
    (Witness.linear .negative case_35_25_16).check 35 25 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_26_1_checked :
    (Witness.rising).check 35 26 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_26_2_checked :
    (Witness.rising).check 35 26 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_26_3_checked :
    (Witness.rising).check 35 26 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_26_4_checked :
    (Witness.rising).check 35 26 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_26_5_checked :
    (Witness.rising).check 35 26 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_26_6_checked :
    (Witness.rising).check 35 26 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_26_7_checked :
    (Witness.rising).check 35 26 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_26_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_35_26_8_checked :
    (Witness.linear .positive case_35_26_8).check 35 26 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_26_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_35_26_9_checked :
    (Witness.linear .positive case_35_26_9).check 35 26 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_26_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_35_26_10_checked :
    (Witness.linear .positive case_35_26_10).check 35 26 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_26_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_35_26_11_checked :
    (Witness.linear .positive case_35_26_11).check 35 26 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_26_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_35_26_12_checked :
    (Witness.linear .positive case_35_26_12).check 35 26 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_26_13 : Certificate := {
  objectiveScale := 704
  eta := 10207446
  rows := #[⟨.assumptionRow 13, 1055⟩]
  caps := #[0, 0, 3255330, 1058200, 351351, 119735, 42150, 15504, 1226244, 887332] }

theorem case_35_26_13_checked :
    (Witness.linear .conditional case_35_26_13).check 35 26 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_26_14 : Certificate := {
  objectiveScale := 985
  eta := 4565928
  rows := #[⟨.assumptionRow 14, 853⟩]
  caps := #[0, 0, 1527484, 595140, 226408, 82885, 32395, 4978722, 4534512, 2846956] }

theorem case_35_26_14_checked :
    (Witness.linear .conditional case_35_26_14).check 35 26 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_26_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 16796, 16796, 11934, 7072] }

theorem case_35_26_15_checked :
    (Witness.linear .negative case_35_26_15).check 35 26 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_26_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 4862, 4862] }

theorem case_35_26_16_checked :
    (Witness.linear .negative case_35_26_16).check 35 26 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_27_1_checked :
    (Witness.rising).check 35 27 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_27_2_checked :
    (Witness.rising).check 35 27 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_27_3_checked :
    (Witness.rising).check 35 27 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_27_4_checked :
    (Witness.rising).check 35 27 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_27_5_checked :
    (Witness.rising).check 35 27 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_27_6_checked :
    (Witness.rising).check 35 27 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_27_7_checked :
    (Witness.rising).check 35 27 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_27_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0] }

theorem case_35_27_8_checked :
    (Witness.linear .positive case_35_27_8).check 35 27 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_27_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1] }

theorem case_35_27_9_checked :
    (Witness.linear .positive case_35_27_9).check 35 27 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_27_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1] }

theorem case_35_27_10_checked :
    (Witness.linear .positive case_35_27_10).check 35 27 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_27_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_35_27_11_checked :
    (Witness.linear .positive case_35_27_11).check 35 27 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_27_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_35_27_12_checked :
    (Witness.linear .positive case_35_27_12).check 35 27 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_27_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_35_27_13_checked :
    (Witness.linear .positive case_35_27_13).check 35 27 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_27_14 : Certificate := {
  objectiveScale := 743
  eta := 8507820
  rows := #[⟨.assumptionRow 14, 770⟩]
  caps := #[0, 0, 2783172, 909636, 324506, 121693, 45320, 6153150, 5341128] }

theorem case_35_27_14_checked :
    (Witness.linear .conditional case_35_27_14).check 35 27 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_27_15 : Certificate := {
  objectiveScale := 49
  eta := 38760
  rows := #[⟨.assumptionRow 15, 27⟩]
  caps := #[0, 0, 19516, 7420, 3822, 1512, 438634, 749360, 606594] }

theorem case_35_27_15_checked :
    (Witness.linear .conditional case_35_27_15).check 35 27 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_27_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 16796, 16796] }

theorem case_35_27_16_checked :
    (Witness.linear .negative case_35_27_16).check 35 27 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_27_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_35_27_17_checked :
    (Witness.linear .negative case_35_27_17).check 35 27 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_28_1_checked :
    (Witness.rising).check 35 28 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_28_2_checked :
    (Witness.rising).check 35 28 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_28_3_checked :
    (Witness.rising).check 35 28 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_28_4_checked :
    (Witness.rising).check 35 28 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_28_5_checked :
    (Witness.rising).check 35 28 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_28_6_checked :
    (Witness.rising).check 35 28 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_28_7_checked :
    (Witness.rising).check 35 28 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_28_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1] }

theorem case_35_28_8_checked :
    (Witness.linear .positive case_35_28_8).check 35 28 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_28_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1] }

theorem case_35_28_9_checked :
    (Witness.linear .positive case_35_28_9).check 35 28 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_28_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2] }

theorem case_35_28_10_checked :
    (Witness.linear .positive case_35_28_10).check 35 28 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_28_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5] }

theorem case_35_28_11_checked :
    (Witness.linear .positive case_35_28_11).check 35 28 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_28_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14] }

theorem case_35_28_12_checked :
    (Witness.linear .positive case_35_28_12).check 35 28 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_28_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42] }

theorem case_35_28_13_checked :
    (Witness.linear .positive case_35_28_13).check 35 28 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_28_14 : Certificate := {
  objectiveScale := 11
  eta := 2074952
  rows := #[⟨.assumptionRow 14, 27⟩]
  caps := #[0, 0, 600780, 176358, 53482, 16588, 5291, 1749] }

theorem case_35_28_14_checked :
    (Witness.linear .conditional case_35_28_14).check 35 28 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_28_15 : Certificate := {
  objectiveScale := 459
  eta := 969000
  rows := #[⟨.assumptionRow 15, 292⟩]
  caps := #[0, 0, 390660, 165676, 60697, 29796, 16620934, 16046640] }

theorem case_35_28_15_checked :
    (Witness.linear .conditional case_35_28_15).check 35 28 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_28_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 58786, 58786] }

theorem case_35_28_16_checked :
    (Witness.linear .negative case_35_28_16).check 35 28 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_28_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_35_28_17_checked :
    (Witness.linear .negative case_35_28_17).check 35 28 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_28_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_35_28_18_checked :
    (Witness.linear .negative case_35_28_18).check 35 28 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_29_1_checked :
    (Witness.rising).check 35 29 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_29_2_checked :
    (Witness.rising).check 35 29 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_29_3_checked :
    (Witness.rising).check 35 29 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_29_4_checked :
    (Witness.rising).check 35 29 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_29_5_checked :
    (Witness.rising).check 35 29 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_29_6_checked :
    (Witness.rising).check 35 29 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_29_7_checked :
    (Witness.rising).check 35 29 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_29_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1] }

theorem case_35_29_8_checked :
    (Witness.linear .positive case_35_29_8).check 35 29 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_29_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2] }

theorem case_35_29_9_checked :
    (Witness.linear .positive case_35_29_9).check 35 29 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_29_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5] }

theorem case_35_29_10_checked :
    (Witness.linear .positive case_35_29_10).check 35 29 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_29_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14] }

theorem case_35_29_11_checked :
    (Witness.linear .positive case_35_29_11).check 35 29 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_29_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42] }

theorem case_35_29_12_checked :
    (Witness.linear .positive case_35_29_12).check 35 29 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_29_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132] }

theorem case_35_29_13_checked :
    (Witness.linear .positive case_35_29_13).check 35 29 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_29_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429] }

theorem case_35_29_14_checked :
    (Witness.linear .positive case_35_29_14).check 35 29 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_29_15 : Certificate := {
  objectiveScale := 659
  eta := 6137646
  rows := #[⟨.assumptionRow 15, 539⟩]
  caps := #[0, 0, 2317848, 825860, 283192, 119756, 39225120] }

theorem case_35_29_15_checked :
    (Witness.linear .conditional case_35_29_15).check 35 29 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_29_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 208012, 208012] }

theorem case_35_29_16_checked :
    (Witness.linear .negative case_35_29_16).check 35 29 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_29_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_35_29_17_checked :
    (Witness.linear .negative case_35_29_17).check 35 29 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_29_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_35_29_18_checked :
    (Witness.linear .negative case_35_29_18).check 35 29 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_30_1_checked :
    (Witness.rising).check 35 30 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_30_2_checked :
    (Witness.rising).check 35 30 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_30_3_checked :
    (Witness.rising).check 35 30 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_30_4_checked :
    (Witness.rising).check 35 30 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_30_5_checked :
    (Witness.rising).check 35 30 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_30_6_checked :
    (Witness.rising).check 35 30 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_30_7_checked :
    (Witness.rising).check 35 30 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_30_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2] }

theorem case_35_30_8_checked :
    (Witness.linear .positive case_35_30_8).check 35 30 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_30_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5] }

theorem case_35_30_9_checked :
    (Witness.linear .positive case_35_30_9).check 35 30 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_30_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_35_30_10_checked :
    (Witness.linear .positive case_35_30_10).check 35 30 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_30_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42] }

theorem case_35_30_11_checked :
    (Witness.linear .positive case_35_30_11).check 35 30 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_30_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132] }

theorem case_35_30_12_checked :
    (Witness.linear .positive case_35_30_12).check 35 30 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_30_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429] }

theorem case_35_30_13_checked :
    (Witness.linear .positive case_35_30_13).check 35 30 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_30_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430] }

theorem case_35_30_14_checked :
    (Witness.linear .positive case_35_30_14).check 35 30 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_30_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862] }

theorem case_35_30_15_checked :
    (Witness.linear .positive case_35_30_15).check 35 30 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_30_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 742900, 742900] }

theorem case_35_30_16_checked :
    (Witness.linear .negative case_35_30_16).check 35 30 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_30_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_35_30_17_checked :
    (Witness.linear .negative case_35_30_17).check 35 30 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_30_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_35_30_18_checked :
    (Witness.linear .negative case_35_30_18).check 35 30 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_30_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_35_30_19_checked :
    (Witness.linear .negative case_35_30_19).check 35 30 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_31_1_checked :
    (Witness.rising).check 35 31 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_31_2_checked :
    (Witness.rising).check 35 31 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_31_3_checked :
    (Witness.rising).check 35 31 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_31_4_checked :
    (Witness.rising).check 35 31 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_31_5_checked :
    (Witness.rising).check 35 31 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_31_6_checked :
    (Witness.rising).check 35 31 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_31_7_checked :
    (Witness.rising).check 35 31 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_31_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5] }

theorem case_35_31_8_checked :
    (Witness.linear .positive case_35_31_8).check 35 31 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_31_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14] }

theorem case_35_31_9_checked :
    (Witness.linear .positive case_35_31_9).check 35 31 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_31_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_35_31_10_checked :
    (Witness.linear .positive case_35_31_10).check 35 31 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_31_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_35_31_11_checked :
    (Witness.linear .positive case_35_31_11).check 35 31 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_31_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429] }

theorem case_35_31_12_checked :
    (Witness.linear .positive case_35_31_12).check 35 31 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_31_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430] }

theorem case_35_31_13_checked :
    (Witness.linear .positive case_35_31_13).check 35 31 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_31_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862] }

theorem case_35_31_14_checked :
    (Witness.linear .positive case_35_31_14).check 35 31 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_31_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796] }

theorem case_35_31_15_checked :
    (Witness.linear .positive case_35_31_15).check 35 31 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_31_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 2674440, 2674440] }

theorem case_35_31_16_checked :
    (Witness.linear .negative case_35_31_16).check 35 31 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_31_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_35_31_17_checked :
    (Witness.linear .negative case_35_31_17).check 35 31 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_31_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_35_31_18_checked :
    (Witness.linear .negative case_35_31_18).check 35 31 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_31_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_35_31_19_checked :
    (Witness.linear .negative case_35_31_19).check 35 31 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_31_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_35_31_20_checked :
    (Witness.linear .negative case_35_31_20).check 35 31 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_32_1_checked :
    (Witness.rising).check 35 32 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_32_2_checked :
    (Witness.rising).check 35 32 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_32_3_checked :
    (Witness.rising).check 35 32 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_32_4_checked :
    (Witness.rising).check 35 32 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_32_5_checked :
    (Witness.rising).check 35 32 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_32_6_checked :
    (Witness.rising).check 35 32 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_32_7_checked :
    (Witness.rising).check 35 32 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_32_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14] }

theorem case_35_32_8_checked :
    (Witness.linear .positive case_35_32_8).check 35 32 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_32_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42] }

theorem case_35_32_9_checked :
    (Witness.linear .positive case_35_32_9).check 35 32 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_32_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_35_32_10_checked :
    (Witness.linear .positive case_35_32_10).check 35 32 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_32_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_35_32_11_checked :
    (Witness.linear .positive case_35_32_11).check 35 32 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_32_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430] }

theorem case_35_32_12_checked :
    (Witness.linear .positive case_35_32_12).check 35 32 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_32_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862] }

theorem case_35_32_13_checked :
    (Witness.linear .positive case_35_32_13).check 35 32 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_32_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796] }

theorem case_35_32_14_checked :
    (Witness.linear .positive case_35_32_14).check 35 32 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_32_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786] }

theorem case_35_32_15_checked :
    (Witness.linear .positive case_35_32_15).check 35 32 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_32_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012] }

theorem case_35_32_16_checked :
    (Witness.linear .positive case_35_32_16).check 35 32 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_32_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_35_32_17_checked :
    (Witness.linear .negative case_35_32_17).check 35 32 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_32_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_35_32_18_checked :
    (Witness.linear .negative case_35_32_18).check 35 32 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_32_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_35_32_19_checked :
    (Witness.linear .negative case_35_32_19).check 35 32 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_32_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_35_32_20_checked :
    (Witness.linear .negative case_35_32_20).check 35 32 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_33_1_checked :
    (Witness.rising).check 35 33 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_33_2_checked :
    (Witness.rising).check 35 33 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_33_3_checked :
    (Witness.rising).check 35 33 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_33_4_checked :
    (Witness.rising).check 35 33 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_33_5_checked :
    (Witness.rising).check 35 33 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_33_6_checked :
    (Witness.rising).check 35 33 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_33_7_checked :
    (Witness.rising).check 35 33 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_33_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42] }

theorem case_35_33_8_checked :
    (Witness.linear .positive case_35_33_8).check 35 33 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_33_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_35_33_9_checked :
    (Witness.linear .positive case_35_33_9).check 35 33 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_33_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_35_33_10_checked :
    (Witness.linear .positive case_35_33_10).check 35 33 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_33_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_35_33_11_checked :
    (Witness.linear .positive case_35_33_11).check 35 33 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_33_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_35_33_12_checked :
    (Witness.linear .positive case_35_33_12).check 35 33 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_33_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796] }

theorem case_35_33_13_checked :
    (Witness.linear .positive case_35_33_13).check 35 33 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_33_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786] }

theorem case_35_33_14_checked :
    (Witness.linear .positive case_35_33_14).check 35 33 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_33_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012] }

theorem case_35_33_15_checked :
    (Witness.linear .positive case_35_33_15).check 35 33 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_33_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900] }

theorem case_35_33_16_checked :
    (Witness.linear .positive case_35_33_16).check 35 33 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_33_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_35_33_17_checked :
    (Witness.linear .negative case_35_33_17).check 35 33 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_33_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_35_33_18_checked :
    (Witness.linear .negative case_35_33_18).check 35 33 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_33_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_35_33_19_checked :
    (Witness.linear .negative case_35_33_19).check 35 33 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_33_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_35_33_20_checked :
    (Witness.linear .negative case_35_33_20).check 35 33 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_33_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_35_33_21_checked :
    (Witness.linear .negative case_35_33_21).check 35 33 21 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_34_1_checked :
    (Witness.rising).check 35 34 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_34_2_checked :
    (Witness.rising).check 35 34 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_34_3_checked :
    (Witness.rising).check 35 34 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_34_4_checked :
    (Witness.rising).check 35 34 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_34_5_checked :
    (Witness.rising).check 35 34 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_35_34_6_checked :
    (Witness.rising).check 35 34 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_34_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0] }

theorem case_35_34_7_checked :
    (Witness.linear .positive case_35_34_7).check 35 34 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_34_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0] }

theorem case_35_34_8_checked :
    (Witness.linear .positive case_35_34_8).check 35 34 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_34_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_35_34_9_checked :
    (Witness.linear .positive case_35_34_9).check 35 34 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_34_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_35_34_10_checked :
    (Witness.linear .positive case_35_34_10).check 35 34 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_34_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_35_34_11_checked :
    (Witness.linear .positive case_35_34_11).check 35 34 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_34_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_35_34_12_checked :
    (Witness.linear .positive case_35_34_12).check 35 34 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_34_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0] }

theorem case_35_34_13_checked :
    (Witness.linear .positive case_35_34_13).check 35 34 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_34_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0] }

theorem case_35_34_14_checked :
    (Witness.linear .positive case_35_34_14).check 35 34 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_34_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0] }

theorem case_35_34_15_checked :
    (Witness.linear .positive case_35_34_15).check 35 34 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_34_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0] }

theorem case_35_34_16_checked :
    (Witness.linear .positive case_35_34_16).check 35 34 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_34_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0] }

theorem case_35_34_17_checked :
    (Witness.linear .positive case_35_34_17).check 35 34 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_34_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_35_34_18_checked :
    (Witness.linear .negative case_35_34_18).check 35 34 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_34_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_35_34_19_checked :
    (Witness.linear .negative case_35_34_19).check 35 34 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_34_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_35_34_20_checked :
    (Witness.linear .negative case_35_34_20).check 35 34 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_34_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_35_34_21_checked :
    (Witness.linear .negative case_35_34_21).check 35 34 21 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_35_34_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_35_34_22_checked :
    (Witness.linear .negative case_35_34_22).check 35 34 22 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_35 (a k : ℕ) (h : Domain 35 a k) :
    ∃ w : Witness, w.check 35 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 18 ≤ a := by omega
  have haHi : a ≤ 34 := by omega
  interval_cases a

  · have hkHi : k ≤ 11 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_35_18_1_checked⟩

    · exact ⟨Witness.rising, case_35_18_2_checked⟩

    · exact ⟨Witness.rising, case_35_18_3_checked⟩

    · exact ⟨Witness.rising, case_35_18_4_checked⟩

    · exact ⟨Witness.rising, case_35_18_5_checked⟩

    · exact ⟨Witness.rising, case_35_18_6_checked⟩

    · exact ⟨Witness.rising, case_35_18_7_checked⟩

    · exact ⟨Witness.linear .positive case_35_18_8, case_35_18_8_checked⟩

    · exact ⟨Witness.linear .positive case_35_18_9, case_35_18_9_checked⟩

    · exact ⟨Witness.linear .positive case_35_18_10, case_35_18_10_checked⟩

    · exact ⟨Witness.linear .conditional case_35_18_11, case_35_18_11_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_35_19_1_checked⟩

    · exact ⟨Witness.rising, case_35_19_2_checked⟩

    · exact ⟨Witness.rising, case_35_19_3_checked⟩

    · exact ⟨Witness.rising, case_35_19_4_checked⟩

    · exact ⟨Witness.rising, case_35_19_5_checked⟩

    · exact ⟨Witness.rising, case_35_19_6_checked⟩

    · exact ⟨Witness.rising, case_35_19_7_checked⟩

    · exact ⟨Witness.linear .positive case_35_19_8, case_35_19_8_checked⟩

    · exact ⟨Witness.linear .positive case_35_19_9, case_35_19_9_checked⟩

    · exact ⟨Witness.linear .positive case_35_19_10, case_35_19_10_checked⟩

    · exact ⟨Witness.linear .conditional case_35_19_11, case_35_19_11_checked⟩

    · exact ⟨Witness.linear .conditional case_35_19_12, case_35_19_12_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_35_20_1_checked⟩

    · exact ⟨Witness.rising, case_35_20_2_checked⟩

    · exact ⟨Witness.rising, case_35_20_3_checked⟩

    · exact ⟨Witness.rising, case_35_20_4_checked⟩

    · exact ⟨Witness.rising, case_35_20_5_checked⟩

    · exact ⟨Witness.rising, case_35_20_6_checked⟩

    · exact ⟨Witness.rising, case_35_20_7_checked⟩

    · exact ⟨Witness.linear .positive case_35_20_8, case_35_20_8_checked⟩

    · exact ⟨Witness.linear .positive case_35_20_9, case_35_20_9_checked⟩

    · exact ⟨Witness.linear .positive case_35_20_10, case_35_20_10_checked⟩

    · exact ⟨Witness.linear .conditional case_35_20_11, case_35_20_11_checked⟩

    · exact ⟨Witness.linear .conditional case_35_20_12, case_35_20_12_checked⟩

  · have hkHi : k ≤ 13 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_35_21_1_checked⟩

    · exact ⟨Witness.rising, case_35_21_2_checked⟩

    · exact ⟨Witness.rising, case_35_21_3_checked⟩

    · exact ⟨Witness.rising, case_35_21_4_checked⟩

    · exact ⟨Witness.rising, case_35_21_5_checked⟩

    · exact ⟨Witness.rising, case_35_21_6_checked⟩

    · exact ⟨Witness.rising, case_35_21_7_checked⟩

    · exact ⟨Witness.linear .positive case_35_21_8, case_35_21_8_checked⟩

    · exact ⟨Witness.linear .positive case_35_21_9, case_35_21_9_checked⟩

    · exact ⟨Witness.linear .positive case_35_21_10, case_35_21_10_checked⟩

    · exact ⟨Witness.linear .conditional case_35_21_11, case_35_21_11_checked⟩

    · exact ⟨Witness.linear .conditional case_35_21_12, case_35_21_12_checked⟩

    · exact ⟨Witness.linear .negative case_35_21_13, case_35_21_13_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_35_22_1_checked⟩

    · exact ⟨Witness.rising, case_35_22_2_checked⟩

    · exact ⟨Witness.rising, case_35_22_3_checked⟩

    · exact ⟨Witness.rising, case_35_22_4_checked⟩

    · exact ⟨Witness.rising, case_35_22_5_checked⟩

    · exact ⟨Witness.rising, case_35_22_6_checked⟩

    · exact ⟨Witness.rising, case_35_22_7_checked⟩

    · exact ⟨Witness.linear .positive case_35_22_8, case_35_22_8_checked⟩

    · exact ⟨Witness.linear .positive case_35_22_9, case_35_22_9_checked⟩

    · exact ⟨Witness.linear .conditional case_35_22_10, case_35_22_10_checked⟩

    · exact ⟨Witness.linear .conditional case_35_22_11, case_35_22_11_checked⟩

    · exact ⟨Witness.linear .conditional case_35_22_12, case_35_22_12_checked⟩

    · exact ⟨Witness.linear .conditional case_35_22_13, case_35_22_13_checked⟩

    · exact ⟨Witness.linear .negative case_35_22_14, case_35_22_14_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_35_23_1_checked⟩

    · exact ⟨Witness.rising, case_35_23_2_checked⟩

    · exact ⟨Witness.rising, case_35_23_3_checked⟩

    · exact ⟨Witness.rising, case_35_23_4_checked⟩

    · exact ⟨Witness.rising, case_35_23_5_checked⟩

    · exact ⟨Witness.rising, case_35_23_6_checked⟩

    · exact ⟨Witness.rising, case_35_23_7_checked⟩

    · exact ⟨Witness.linear .positive case_35_23_8, case_35_23_8_checked⟩

    · exact ⟨Witness.linear .positive case_35_23_9, case_35_23_9_checked⟩

    · exact ⟨Witness.linear .positive case_35_23_10, case_35_23_10_checked⟩

    · exact ⟨Witness.linear .conditional case_35_23_11, case_35_23_11_checked⟩

    · exact ⟨Witness.linear .conditional case_35_23_12, case_35_23_12_checked⟩

    · exact ⟨Witness.linear .conditional case_35_23_13, case_35_23_13_checked⟩

    · exact ⟨Witness.linear .negative case_35_23_14, case_35_23_14_checked⟩

  · have hkHi : k ≤ 15 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_35_24_1_checked⟩

    · exact ⟨Witness.rising, case_35_24_2_checked⟩

    · exact ⟨Witness.rising, case_35_24_3_checked⟩

    · exact ⟨Witness.rising, case_35_24_4_checked⟩

    · exact ⟨Witness.rising, case_35_24_5_checked⟩

    · exact ⟨Witness.rising, case_35_24_6_checked⟩

    · exact ⟨Witness.rising, case_35_24_7_checked⟩

    · exact ⟨Witness.linear .positive case_35_24_8, case_35_24_8_checked⟩

    · exact ⟨Witness.linear .positive case_35_24_9, case_35_24_9_checked⟩

    · exact ⟨Witness.linear .positive case_35_24_10, case_35_24_10_checked⟩

    · exact ⟨Witness.linear .positive case_35_24_11, case_35_24_11_checked⟩

    · exact ⟨Witness.linear .conditional case_35_24_12, case_35_24_12_checked⟩

    · exact ⟨Witness.linear .conditional case_35_24_13, case_35_24_13_checked⟩

    · exact ⟨Witness.linear .negative case_35_24_14, case_35_24_14_checked⟩

    · exact ⟨Witness.linear .negative case_35_24_15, case_35_24_15_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_35_25_1_checked⟩

    · exact ⟨Witness.rising, case_35_25_2_checked⟩

    · exact ⟨Witness.rising, case_35_25_3_checked⟩

    · exact ⟨Witness.rising, case_35_25_4_checked⟩

    · exact ⟨Witness.rising, case_35_25_5_checked⟩

    · exact ⟨Witness.rising, case_35_25_6_checked⟩

    · exact ⟨Witness.rising, case_35_25_7_checked⟩

    · exact ⟨Witness.linear .positive case_35_25_8, case_35_25_8_checked⟩

    · exact ⟨Witness.linear .positive case_35_25_9, case_35_25_9_checked⟩

    · exact ⟨Witness.linear .positive case_35_25_10, case_35_25_10_checked⟩

    · exact ⟨Witness.linear .positive case_35_25_11, case_35_25_11_checked⟩

    · exact ⟨Witness.linear .positive case_35_25_12, case_35_25_12_checked⟩

    · exact ⟨Witness.linear .conditional case_35_25_13, case_35_25_13_checked⟩

    · exact ⟨Witness.linear .conditional case_35_25_14, case_35_25_14_checked⟩

    · exact ⟨Witness.linear .negative case_35_25_15, case_35_25_15_checked⟩

    · exact ⟨Witness.linear .negative case_35_25_16, case_35_25_16_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_35_26_1_checked⟩

    · exact ⟨Witness.rising, case_35_26_2_checked⟩

    · exact ⟨Witness.rising, case_35_26_3_checked⟩

    · exact ⟨Witness.rising, case_35_26_4_checked⟩

    · exact ⟨Witness.rising, case_35_26_5_checked⟩

    · exact ⟨Witness.rising, case_35_26_6_checked⟩

    · exact ⟨Witness.rising, case_35_26_7_checked⟩

    · exact ⟨Witness.linear .positive case_35_26_8, case_35_26_8_checked⟩

    · exact ⟨Witness.linear .positive case_35_26_9, case_35_26_9_checked⟩

    · exact ⟨Witness.linear .positive case_35_26_10, case_35_26_10_checked⟩

    · exact ⟨Witness.linear .positive case_35_26_11, case_35_26_11_checked⟩

    · exact ⟨Witness.linear .positive case_35_26_12, case_35_26_12_checked⟩

    · exact ⟨Witness.linear .conditional case_35_26_13, case_35_26_13_checked⟩

    · exact ⟨Witness.linear .conditional case_35_26_14, case_35_26_14_checked⟩

    · exact ⟨Witness.linear .negative case_35_26_15, case_35_26_15_checked⟩

    · exact ⟨Witness.linear .negative case_35_26_16, case_35_26_16_checked⟩

  · have hkHi : k ≤ 17 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_35_27_1_checked⟩

    · exact ⟨Witness.rising, case_35_27_2_checked⟩

    · exact ⟨Witness.rising, case_35_27_3_checked⟩

    · exact ⟨Witness.rising, case_35_27_4_checked⟩

    · exact ⟨Witness.rising, case_35_27_5_checked⟩

    · exact ⟨Witness.rising, case_35_27_6_checked⟩

    · exact ⟨Witness.rising, case_35_27_7_checked⟩

    · exact ⟨Witness.linear .positive case_35_27_8, case_35_27_8_checked⟩

    · exact ⟨Witness.linear .positive case_35_27_9, case_35_27_9_checked⟩

    · exact ⟨Witness.linear .positive case_35_27_10, case_35_27_10_checked⟩

    · exact ⟨Witness.linear .positive case_35_27_11, case_35_27_11_checked⟩

    · exact ⟨Witness.linear .positive case_35_27_12, case_35_27_12_checked⟩

    · exact ⟨Witness.linear .positive case_35_27_13, case_35_27_13_checked⟩

    · exact ⟨Witness.linear .conditional case_35_27_14, case_35_27_14_checked⟩

    · exact ⟨Witness.linear .conditional case_35_27_15, case_35_27_15_checked⟩

    · exact ⟨Witness.linear .negative case_35_27_16, case_35_27_16_checked⟩

    · exact ⟨Witness.linear .negative case_35_27_17, case_35_27_17_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_35_28_1_checked⟩

    · exact ⟨Witness.rising, case_35_28_2_checked⟩

    · exact ⟨Witness.rising, case_35_28_3_checked⟩

    · exact ⟨Witness.rising, case_35_28_4_checked⟩

    · exact ⟨Witness.rising, case_35_28_5_checked⟩

    · exact ⟨Witness.rising, case_35_28_6_checked⟩

    · exact ⟨Witness.rising, case_35_28_7_checked⟩

    · exact ⟨Witness.linear .positive case_35_28_8, case_35_28_8_checked⟩

    · exact ⟨Witness.linear .positive case_35_28_9, case_35_28_9_checked⟩

    · exact ⟨Witness.linear .positive case_35_28_10, case_35_28_10_checked⟩

    · exact ⟨Witness.linear .positive case_35_28_11, case_35_28_11_checked⟩

    · exact ⟨Witness.linear .positive case_35_28_12, case_35_28_12_checked⟩

    · exact ⟨Witness.linear .positive case_35_28_13, case_35_28_13_checked⟩

    · exact ⟨Witness.linear .conditional case_35_28_14, case_35_28_14_checked⟩

    · exact ⟨Witness.linear .conditional case_35_28_15, case_35_28_15_checked⟩

    · exact ⟨Witness.linear .negative case_35_28_16, case_35_28_16_checked⟩

    · exact ⟨Witness.linear .negative case_35_28_17, case_35_28_17_checked⟩

    · exact ⟨Witness.linear .negative case_35_28_18, case_35_28_18_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_35_29_1_checked⟩

    · exact ⟨Witness.rising, case_35_29_2_checked⟩

    · exact ⟨Witness.rising, case_35_29_3_checked⟩

    · exact ⟨Witness.rising, case_35_29_4_checked⟩

    · exact ⟨Witness.rising, case_35_29_5_checked⟩

    · exact ⟨Witness.rising, case_35_29_6_checked⟩

    · exact ⟨Witness.rising, case_35_29_7_checked⟩

    · exact ⟨Witness.linear .positive case_35_29_8, case_35_29_8_checked⟩

    · exact ⟨Witness.linear .positive case_35_29_9, case_35_29_9_checked⟩

    · exact ⟨Witness.linear .positive case_35_29_10, case_35_29_10_checked⟩

    · exact ⟨Witness.linear .positive case_35_29_11, case_35_29_11_checked⟩

    · exact ⟨Witness.linear .positive case_35_29_12, case_35_29_12_checked⟩

    · exact ⟨Witness.linear .positive case_35_29_13, case_35_29_13_checked⟩

    · exact ⟨Witness.linear .positive case_35_29_14, case_35_29_14_checked⟩

    · exact ⟨Witness.linear .conditional case_35_29_15, case_35_29_15_checked⟩

    · exact ⟨Witness.linear .negative case_35_29_16, case_35_29_16_checked⟩

    · exact ⟨Witness.linear .negative case_35_29_17, case_35_29_17_checked⟩

    · exact ⟨Witness.linear .negative case_35_29_18, case_35_29_18_checked⟩

  · have hkHi : k ≤ 19 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_35_30_1_checked⟩

    · exact ⟨Witness.rising, case_35_30_2_checked⟩

    · exact ⟨Witness.rising, case_35_30_3_checked⟩

    · exact ⟨Witness.rising, case_35_30_4_checked⟩

    · exact ⟨Witness.rising, case_35_30_5_checked⟩

    · exact ⟨Witness.rising, case_35_30_6_checked⟩

    · exact ⟨Witness.rising, case_35_30_7_checked⟩

    · exact ⟨Witness.linear .positive case_35_30_8, case_35_30_8_checked⟩

    · exact ⟨Witness.linear .positive case_35_30_9, case_35_30_9_checked⟩

    · exact ⟨Witness.linear .positive case_35_30_10, case_35_30_10_checked⟩

    · exact ⟨Witness.linear .positive case_35_30_11, case_35_30_11_checked⟩

    · exact ⟨Witness.linear .positive case_35_30_12, case_35_30_12_checked⟩

    · exact ⟨Witness.linear .positive case_35_30_13, case_35_30_13_checked⟩

    · exact ⟨Witness.linear .positive case_35_30_14, case_35_30_14_checked⟩

    · exact ⟨Witness.linear .positive case_35_30_15, case_35_30_15_checked⟩

    · exact ⟨Witness.linear .negative case_35_30_16, case_35_30_16_checked⟩

    · exact ⟨Witness.linear .negative case_35_30_17, case_35_30_17_checked⟩

    · exact ⟨Witness.linear .negative case_35_30_18, case_35_30_18_checked⟩

    · exact ⟨Witness.linear .negative case_35_30_19, case_35_30_19_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_35_31_1_checked⟩

    · exact ⟨Witness.rising, case_35_31_2_checked⟩

    · exact ⟨Witness.rising, case_35_31_3_checked⟩

    · exact ⟨Witness.rising, case_35_31_4_checked⟩

    · exact ⟨Witness.rising, case_35_31_5_checked⟩

    · exact ⟨Witness.rising, case_35_31_6_checked⟩

    · exact ⟨Witness.rising, case_35_31_7_checked⟩

    · exact ⟨Witness.linear .positive case_35_31_8, case_35_31_8_checked⟩

    · exact ⟨Witness.linear .positive case_35_31_9, case_35_31_9_checked⟩

    · exact ⟨Witness.linear .positive case_35_31_10, case_35_31_10_checked⟩

    · exact ⟨Witness.linear .positive case_35_31_11, case_35_31_11_checked⟩

    · exact ⟨Witness.linear .positive case_35_31_12, case_35_31_12_checked⟩

    · exact ⟨Witness.linear .positive case_35_31_13, case_35_31_13_checked⟩

    · exact ⟨Witness.linear .positive case_35_31_14, case_35_31_14_checked⟩

    · exact ⟨Witness.linear .positive case_35_31_15, case_35_31_15_checked⟩

    · exact ⟨Witness.linear .negative case_35_31_16, case_35_31_16_checked⟩

    · exact ⟨Witness.linear .negative case_35_31_17, case_35_31_17_checked⟩

    · exact ⟨Witness.linear .negative case_35_31_18, case_35_31_18_checked⟩

    · exact ⟨Witness.linear .negative case_35_31_19, case_35_31_19_checked⟩

    · exact ⟨Witness.linear .negative case_35_31_20, case_35_31_20_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_35_32_1_checked⟩

    · exact ⟨Witness.rising, case_35_32_2_checked⟩

    · exact ⟨Witness.rising, case_35_32_3_checked⟩

    · exact ⟨Witness.rising, case_35_32_4_checked⟩

    · exact ⟨Witness.rising, case_35_32_5_checked⟩

    · exact ⟨Witness.rising, case_35_32_6_checked⟩

    · exact ⟨Witness.rising, case_35_32_7_checked⟩

    · exact ⟨Witness.linear .positive case_35_32_8, case_35_32_8_checked⟩

    · exact ⟨Witness.linear .positive case_35_32_9, case_35_32_9_checked⟩

    · exact ⟨Witness.linear .positive case_35_32_10, case_35_32_10_checked⟩

    · exact ⟨Witness.linear .positive case_35_32_11, case_35_32_11_checked⟩

    · exact ⟨Witness.linear .positive case_35_32_12, case_35_32_12_checked⟩

    · exact ⟨Witness.linear .positive case_35_32_13, case_35_32_13_checked⟩

    · exact ⟨Witness.linear .positive case_35_32_14, case_35_32_14_checked⟩

    · exact ⟨Witness.linear .positive case_35_32_15, case_35_32_15_checked⟩

    · exact ⟨Witness.linear .positive case_35_32_16, case_35_32_16_checked⟩

    · exact ⟨Witness.linear .negative case_35_32_17, case_35_32_17_checked⟩

    · exact ⟨Witness.linear .negative case_35_32_18, case_35_32_18_checked⟩

    · exact ⟨Witness.linear .negative case_35_32_19, case_35_32_19_checked⟩

    · exact ⟨Witness.linear .negative case_35_32_20, case_35_32_20_checked⟩

  · have hkHi : k ≤ 21 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_35_33_1_checked⟩

    · exact ⟨Witness.rising, case_35_33_2_checked⟩

    · exact ⟨Witness.rising, case_35_33_3_checked⟩

    · exact ⟨Witness.rising, case_35_33_4_checked⟩

    · exact ⟨Witness.rising, case_35_33_5_checked⟩

    · exact ⟨Witness.rising, case_35_33_6_checked⟩

    · exact ⟨Witness.rising, case_35_33_7_checked⟩

    · exact ⟨Witness.linear .positive case_35_33_8, case_35_33_8_checked⟩

    · exact ⟨Witness.linear .positive case_35_33_9, case_35_33_9_checked⟩

    · exact ⟨Witness.linear .positive case_35_33_10, case_35_33_10_checked⟩

    · exact ⟨Witness.linear .positive case_35_33_11, case_35_33_11_checked⟩

    · exact ⟨Witness.linear .positive case_35_33_12, case_35_33_12_checked⟩

    · exact ⟨Witness.linear .positive case_35_33_13, case_35_33_13_checked⟩

    · exact ⟨Witness.linear .positive case_35_33_14, case_35_33_14_checked⟩

    · exact ⟨Witness.linear .positive case_35_33_15, case_35_33_15_checked⟩

    · exact ⟨Witness.linear .positive case_35_33_16, case_35_33_16_checked⟩

    · exact ⟨Witness.linear .negative case_35_33_17, case_35_33_17_checked⟩

    · exact ⟨Witness.linear .negative case_35_33_18, case_35_33_18_checked⟩

    · exact ⟨Witness.linear .negative case_35_33_19, case_35_33_19_checked⟩

    · exact ⟨Witness.linear .negative case_35_33_20, case_35_33_20_checked⟩

    · exact ⟨Witness.linear .negative case_35_33_21, case_35_33_21_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_35_34_1_checked⟩

    · exact ⟨Witness.rising, case_35_34_2_checked⟩

    · exact ⟨Witness.rising, case_35_34_3_checked⟩

    · exact ⟨Witness.rising, case_35_34_4_checked⟩

    · exact ⟨Witness.rising, case_35_34_5_checked⟩

    · exact ⟨Witness.rising, case_35_34_6_checked⟩

    · exact ⟨Witness.linear .positive case_35_34_7, case_35_34_7_checked⟩

    · exact ⟨Witness.linear .positive case_35_34_8, case_35_34_8_checked⟩

    · exact ⟨Witness.linear .positive case_35_34_9, case_35_34_9_checked⟩

    · exact ⟨Witness.linear .positive case_35_34_10, case_35_34_10_checked⟩

    · exact ⟨Witness.linear .positive case_35_34_11, case_35_34_11_checked⟩

    · exact ⟨Witness.linear .positive case_35_34_12, case_35_34_12_checked⟩

    · exact ⟨Witness.linear .positive case_35_34_13, case_35_34_13_checked⟩

    · exact ⟨Witness.linear .positive case_35_34_14, case_35_34_14_checked⟩

    · exact ⟨Witness.linear .positive case_35_34_15, case_35_34_15_checked⟩

    · exact ⟨Witness.linear .positive case_35_34_16, case_35_34_16_checked⟩

    · exact ⟨Witness.linear .positive case_35_34_17, case_35_34_17_checked⟩

    · exact ⟨Witness.linear .negative case_35_34_18, case_35_34_18_checked⟩

    · exact ⟨Witness.linear .negative case_35_34_19, case_35_34_19_checked⟩

    · exact ⟨Witness.linear .negative case_35_34_20, case_35_34_20_checked⟩

    · exact ⟨Witness.linear .negative case_35_34_21, case_35_34_21_checked⟩

    · exact ⟨Witness.linear .negative case_35_34_22, case_35_34_22_checked⟩


#print axioms coverage_35
end ForestUnimodality.FiniteRows.FiniteData
