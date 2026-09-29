import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell187.Parameters
import ForestUnimodality.BinomialMassData.Q2567_4752.Batch000_049
import ForestUnimodality.BinomialMassData.Q2567_4752.Batch050_099
import ForestUnimodality.BinomialMassData.Q643_1188.Batch000_049
import ForestUnimodality.BinomialMassData.Q643_1188.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree000.table
  base := (85285334693353043014596437/2500000000000000000000000)
  polynomial :=
    { denominator := 11880000000000000000000000000000000000000000
      center := (48773)
      previous := (0)
      next := (41515)
      square := (2101436917087941855797339487600000000000000)
      linear := (-7772771420098520391839258514000000000000000)
      constant := (405275910462813660405362268624000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree000.table
  base := (85285334693353043014596437/2500000000000000000000000)
  polynomial :=
    { denominator := 2970000000000000000000000000000000000000000
      center := (12217)
      previous := (0)
      next := (10355)
      square := (525359229271985463949334871900000000000000)
      linear := (-1943192855024630097959814628500000000000000)
      constant := (101318977615703415101340567156000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 0 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 0 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree001.table
  base := (209670386989236667817481205565674569461803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-2982811682539853899355231086741650000000000000)
      constant := (75408430565564222310714490676797888328124723308) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree001.table
  base := (209417938157035200518295667826196454983689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-746031270153258465753776105980350000000000000)
      constant := (18830624175170624159049134564781231847656223001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 1 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 1 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49829588068185814597/100000000000000000000)
  directionHi := (24914794034092907299/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree002.table
  base := (66484885190923735278834486050963571713381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-3657110253310447242334202394825300000000000000)
      constant := (50139113480345074929617035484185959328124997032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree002.table
  base := (66339071070459059590414771448301793737919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-914934262364201792413487267296200000000000000)
      constant := (12510978810324652424450880752304830847656194142) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 2 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 2 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49829588068185814597/100000000000000000000)
  centralHi := (24914794034092907299/50000000000000000000)
  directionLo := (70469679253492932331/100000000000000000000)
  directionHi := (17617419813373233083/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree003.table
  base := (86968625974210431014852538400267262215461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1609509)
      previous := (0)
      next := (1369995)
      square := (69347418263902081241312203090800000000000000)
      linear := (-481267647120115620590352633656550000000000000)
      constant := (4007325238048154878594830253378363685394933044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree003.table
  base := (43355075630100051552038255404531724661577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (403161)
      previous := (0)
      next := (341715)
      square := (17336854565975520310328050772700000000000000)
      linear := (-120426361619460568785910936512450000000000000)
      constant := (999677959814454508222485749585649616816232354) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 3 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 3 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70469679253492932331/100000000000000000000)
  centralHi := (17617419813373233083/25000000000000000000)
  directionLo := (86307378254325732397/100000000000000000000)
  directionHi := (43153689127162866199/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree004.table
  base := (58422664137269900999048832857715527443601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-5005707394851633928292145010992600000000000000)
      constant := (28515809376271700559162934013346990841090402436) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree004.table
  base := (58213349764522446013972521932657258697383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-1252740246786088445732909589927900000000000000)
      constant := (7115758644463547485974691792785564132437457047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 4 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 4 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86307378254325732397/100000000000000000000)
  centralHi := (43153689127162866199/50000000000000000000)
  directionLo := (19931835227274325839/20000000000000000000)
  directionHi := (24914794034092907299/25000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree005.table
  base := (2499519980199993040817806740486334644763/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-5680005965622227271271116319076250000000000000)
      constant := (24899097359248223222127946534270680369013565888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree005.table
  base := (39828321999826923148540663109977706530039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-1421643238997031772392620751243750000000000000)
      constant := (6217783133296201212338619359147242265308210151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 5 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 5 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19931835227274325839/20000000000000000000)
  centralHi := (24914794034092907299/25000000000000000000)
  directionLo := (111422346211275907199/100000000000000000000)
  directionHi := (34819483191023721/31250000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree006.table
  base := (13785069634014561858248349758737675272769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1609509)
      previous := (0)
      next := (1369995)
      square := (69347418263902081241312203090800000000000000)
      linear := (-706033837376980068250009736351100000000000000)
      constant := (2640725964809946086958601267726997392787271752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree006.table
  base := (1715158107680371418664297438890455073767/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (403161)
      previous := (0)
      next := (341715)
      square := (17336854565975520310328050772700000000000000)
      linear := (-176727359023108344339147990284400000000000000)
      constant := (660045802103465456355627801406870602847845872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 6 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 6 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111422346211275907199/100000000000000000000)
  centralHi := (34819483191023721/31250000000000000)
  directionLo := (122057064860132191423/100000000000000000000)
  directionHi := (1907141638439565491/1562500000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree007.table
  base := (753051226206224140781782764187747202457/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-7028603107163413957229058935243550000000000000)
      constant := (24296066133001871026681073456898210235652951300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree007.table
  base := (18726387756958943769881840134257836910341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-1759449223418918425712043073875450000000000000)
      constant := (6078155522513403034630626845598168286024269269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 7 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 7 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122057064860132191423/100000000000000000000)
  centralHi := (1907141638439565491/1562500000000000000)
  directionLo := (102997420282196171/78125000000000000)
  directionHi := (131836697961211098881/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree008.table
  base := (1241572623694533032222143731520816658971/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-7702901677934007300208030243327200000000000000)
      constant := (26013124075778142727695794846478088666846917560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree008.table
  base := (12336620913596405425419632668661881741451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-1928352215629861752371754235191300000000000000)
      constant := (6512524082944899202307277188330195926531651259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 8 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 8 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102997420282196171/78125000000000000)
  centralHi := (131836697961211098881/100000000000000000000)
  directionLo := (140939358506985864663/100000000000000000000)
  directionHi := (17617419813373233083/12500000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree009.table
  base := (3772222752610946238163752073768758966127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (536503)
      previous := (0)
      next := (456665)
      square := (23115806087967360413770734363600000000000000)
      linear := (-310266675877948171969888946348550000000000000)
      constant := (1060649813453162870569161146109628096838695272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree009.table
  base := (7481002011901604680121884381087287861323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (134387)
      previous := (0)
      next := (113905)
      square := (5778951521991840103442683590900000000000000)
      linear := (-77676118808918706630795014685450000000000000)
      constant := (265690234549109576756893663356818419442942241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 9 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 9 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140939358506985864663/100000000000000000000)
  centralHi := (17617419813373233083/12500000000000000000)
  directionLo := (9343047762784840237/6250000000000000000)
  directionHi := (149488764204557443793/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree010.table
  base := (74615838195731105089977685726872121373/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-9051498819475193986165972859494500000000000000)
      constant := (31999386553187714593431577913221176340838191400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree010.table
  base := (3679329660138107495107058837249478093771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-2266158200051748405691176557823000000000000000)
      constant := (8019134187592902034881480565178064213173446139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 10 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 10 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9343047762784840237/6250000000000000000)
  centralHi := (149488764204557443793/100000000000000000000)
  directionLo := (157574993163416830983/100000000000000000000)
  directionHi := (19696874145427103873/12500000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree011.table
  base := (336673992453505755294082737270649185309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320760000000000000000000000000000000000000000
      center := (1316871)
      previous := (0)
      next := (1120905)
      square := (56738796761374430106528166165200000000000000)
      linear := (-884163399113253393558631287961650000000000000)
      constant := (3272027082972360878879127945465531999035942968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree011.table
  base := (315616211835105181371376366207614169049/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80190000000000000000000000000000000000000000
      center := (329859)
      previous := (0)
      next := (279585)
      square := (14184699190343607526632041541300000000000000)
      linear := (-221369199296608339304626156285350000000000000)
      constant := (820229289397086256267144135350443966043207862) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 11 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 11 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157574993163416830983/100000000000000000000)
  centralHi := (19696874145427103873/12500000000000000000)
  directionLo := (165266047080142711101/100000000000000000000)
  directionHi := (82633023540071355551/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree012.table
  base := (-911493149756100158115353853203180739999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1609509)
      previous := (0)
      next := (1369995)
      square := (69347418263902081241312203090800000000000000)
      linear := (-1155566217890708963569323941740200000000000000)
      constant := (4505271191949044494756468590667120004538158408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree012.table
  base := (-464416859234845626011947137763849554113/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (403161)
      previous := (0)
      next := (341715)
      square := (17336854565975520310328050772700000000000000)
      linear := (-289329353830403895445622097828300000000000000)
      constant := (1129628272681452722280576692621906042080553948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 12 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 12 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165266047080142711101/100000000000000000000)
  centralHi := (82633023540071355551/50000000000000000000)
  directionLo := (86307378254325732397/50000000000000000000)
  directionHi := (34522951301730292959/20000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree013.table
  base := (-3888878401215946371592958850861399622661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-11074394531786974015102886783745450000000000000)
      constant := (45618710814603139357483657908730540640238783404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree013.table
  base := (-1958773603762249702074610089533613033441/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-2772867176684578385670310041770550000000000000)
      constant := (11440048191682162919224978251875577805866405662) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 13 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 13 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86307378254325732397/50000000000000000000)
  centralHi := (34522951301730292959/20000000000000000000)
  directionLo := (179663134815092546103/100000000000000000000)
  directionHi := (22457891851886568263/12500000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree014.table
  base := (-5614713942068213374109962931580029353013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-11748693102557567358081858091829100000000000000)
      constant := (51174216872605184763848766078412822513200305132) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree014.table
  base := (-4510766896584025622822024322085642421/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-2941770168895521712330021203086400000000000000)
      constant := (12834760022730340823869530686058859459607513750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 14 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 14 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179663134815092546103/100000000000000000000)
  centralHi := (22457891851886568263/12500000000000000000)
  directionLo := (186445246275230105241/100000000000000000000)
  directionHi := (93222623137615052621/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree015.table
  base := (-883104066237437006865260615039819195919/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1609509)
      previous := (0)
      next := (1369995)
      square := (69347418263902081241312203090800000000000000)
      linear := (-1380332408147573411228981044434750000000000000)
      constant := (6354584174631006248105211112208479863445532192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree015.table
  base := (-7084509193444371767530062399936176207909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (403161)
      previous := (0)
      next := (341715)
      square := (17336854565975520310328050772700000000000000)
      linear := (-345630351234051670998859151600250000000000000)
      constant := (1593903898591155566478633193526194286986283891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 15 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 15 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186445246275230105241/100000000000000000000)
  centralHi := (93222623137615052621/50000000000000000000)
  directionLo := (48247291184114867579/25000000000000000000)
  directionHi := (192989164736459470317/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree016.table
  base := (-1657229503080387727886729890734496564559/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-13097290244098754044039800707996400000000000000)
      constant := (63653280192819940364863299415643215850736303380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree016.table
  base := (-8302445655767518483831004449621972865787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-3279576153317408365649443525718100000000000000)
      constant := (15967049903136949854652854945042095395481794517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 16 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 16 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48247291184114867579/25000000000000000000)
  centralHi := (192989164736459470317/100000000000000000000)
  directionLo := (19931835227274325839/10000000000000000000)
  directionHi := (199318352272743258391/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree017.table
  base := (-74508235841595647671154678122113589007/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-13771588814869347387018772016080050000000000000)
      constant := (70547981139489981546199152826475127151140768500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree017.table
  base := (-1865402857880037066739717043220111717711/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-3448479145528351692309154687033950000000000000)
      constant := (17697439535417451886103735113716654577462152005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 17 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 17 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19931835227274325839/10000000000000000000)
  centralHi := (199318352272743258391/100000000000000000000)
  directionLo := (8218106195445903459/4000000000000000000)
  directionHi := (51363163721536896619/25000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree018.table
  base := (-508664175613314949421506348472042873671/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (536503)
      previous := (0)
      next := (456665)
      square := (23115806087967360413770734363600000000000000)
      linear := (-535032866134812619629546049043100000000000000)
      constant := (2883928852950692479996107696508528124537347440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree018.table
  base := (-63652649098599808329872217049614065517/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (134387)
      previous := (0)
      next := (113905)
      square := (5778951521991840103442683590900000000000000)
      linear := (-133977116212566482184032068457400000000000000)
      constant := (723481190204615186426190928684800735672953760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 18 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 18 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8218106195445903459/4000000000000000000)
  centralHi := (51363163721536896619/25000000000000000000)
  directionLo := (42281807552095759399/20000000000000000000)
  directionHi := (52852259440119699249/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree019.table
  base := (-10885473301429521580015638720548072180549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-15120185956410534072976714632247350000000000000)
      constant := (85600494671292268233035249922899923841603813036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree019.table
  base := (-2178932184292760589016460342160814226303/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-3786285129950238345628577009665650000000000000)
      constant := (21474944708407945333145398866258452439560193365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 19 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 19 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42281807552095759399/20000000000000000000)
  centralHi := (52852259440119699249/25000000000000000000)
  directionLo := (217202138787482099563/100000000000000000000)
  directionHi := (54300534696870524891/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree020.table
  base := (-11465525733066011666662637997699737810287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-15794484527181127415955685940331000000000000000)
      constant := (93745784903831855734888039011305490309969576068) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree020.table
  base := (-11473089086103915168574907391275677749341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-3955188122161181672288288170981500000000000000)
      constant := (23518942046306792825336700012107963741408379731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 20 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 20 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217202138787482099563/100000000000000000000)
  centralHi := (54300534696870524891/25000000000000000000)
  directionLo := (222844692422551814399/100000000000000000000)
  directionHi := (34819483191023721/15625000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree021.table
  base := (-11925371233001297648676628842487248502449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1609509)
      previous := (0)
      next := (1369995)
      square := (69347418263902081241312203090800000000000000)
      linear := (-1829864788661302306548295249823850000000000000)
      constant := (11366415582617875925200342471880890847209989404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree021.table
  base := (-5965792991673085490053453109510156055893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (403161)
      previous := (0)
      next := (341715)
      square := (17336854565975520310328050772700000000000000)
      linear := (-458232346041347222105333259144150000000000000)
      constant := (2851659603892725730037570880863050670992385414) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 21 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 21 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222844692422551814399/100000000000000000000)
  centralHi := (34819483191023721/15625000000000000)
  directionLo := (228347859170929842437/100000000000000000000)
  directionHi := (114173929585464921219/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree022.table
  base := (-12274274144306679670185889199469587515467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320760000000000000000000000000000000000000000
      center := (1316871)
      previous := (0)
      next := (1120905)
      square := (56738796761374430106528166165200000000000000)
      linear := (-1558461969883846736537602596045300000000000000)
      constant := (10113917445157040522829703141174644760853880508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree022.table
  base := (-6139685745939244106080377178627588100291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80190000000000000000000000000000000000000000
      center := (329859)
      previous := (0)
      next := (279585)
      square := (14184699190343607526632041541300000000000000)
      linear := (-390272191507551665964337317601200000000000000)
      constant := (2537464963482907184005842512503245742047532942) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 22 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 22 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228347859170929842437/100000000000000000000)
  centralHi := (114173929585464921219/50000000000000000000)
  directionLo := (46744297036105653367/20000000000000000000)
  directionHi := (58430371295132066709/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree023.table
  base := (-1251944930024126933894435745573078313369/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-17817380239492907444892599864581950000000000000)
      constant := (120609294210423731104625527324539534339741355160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree023.table
  base := (-3130905705812431381622021398226498586907/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-4461897098794011652267421654929050000000000000)
      constant := (30259843441485621912820639276701773894590081748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 23 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 23 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46744297036105653367/20000000000000000000)
  centralHi := (58430371295132066709/25000000000000000000)
  directionLo := (119487154625546444503/50000000000000000000)
  directionHi := (238974309251092889007/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree024.table
  base := (-12666526776877455552281296290836513399851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1609509)
      previous := (0)
      next := (1369995)
      square := (69347418263902081241312203090800000000000000)
      linear := (-2054630978918166754207952352518400000000000000)
      constant := (14484928965680962442035710314997345328672241396) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree024.table
  base := (-6334969092595052775810675941697577732739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (403161)
      previous := (0)
      next := (341715)
      square := (17336854565975520310328050772700000000000000)
      linear := (-514533343444994997658570312916100000000000000)
      constant := (3634181016916642780974114865617044081282850122) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 24 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 24 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119487154625546444503/50000000000000000000)
  centralHi := (238974309251092889007/100000000000000000000)
  directionLo := (244114129720264382847/100000000000000000000)
  directionHi := (1907141638439565491/781250000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree025.table
  base := (-3179976541894346382672411736507017899501/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-19165977381034094130850542480749250000000000000)
      constant := (140516739003918711795524483668436200267146660656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree025.table
  base := (-12722690203867751905915841143732903457611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-4799703083215898305586843977560750000000000000)
      constant := (35255086025622804355651949587395433068907591301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 25 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 25 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244114129720264382847/100000000000000000000)
  centralHi := (1907141638439565491/781250000000000000)
  directionLo := (249147940340929072987/100000000000000000000)
  directionHi := (62286985085232268247/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree026.table
  base := (-3170757217089005850783282826595556655179/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-19840275951804687473829513788832900000000000000)
      constant := (151065214900389544672827756049876864438053049424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree026.table
  base := (-12685297507714475346430722367285897765759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-4968606075426841632246555138876600000000000000)
      constant := (37901912507809338298405954429492003243980164369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 26 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 26 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249147940340929072987/100000000000000000000)
  centralHi := (62286985085232268247/25000000000000000000)
  directionLo := (50816408382793933407/20000000000000000000)
  directionHi := (63520510478492416759/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree027.table
  base := (-12558588587255056162162905324323505095223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (536503)
      previous := (0)
      next := (456665)
      square := (23115806087967360413770734363600000000000000)
      linear := (-759799056391677067289203151737650000000000000)
      constant := (6000327331235946812538052974728460747915625836) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree027.table
  base := (-12560434639656417383259254103935896253959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (134387)
      previous := (0)
      next := (113905)
      square := (5778951521991840103442683590900000000000000)
      linear := (-190278113616214257737269122229350000000000000)
      constant := (1505476765927867216317230817533947676938315947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 27 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 27 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50816408382793933407/20000000000000000000)
  centralHi := (63520510478492416759/25000000000000000000)
  directionLo := (32365266845372149649/12500000000000000000)
  directionHi := (258922134762977197193/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree028.table
  base := (-12348694776649318577648164119355117188799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-21188873093345874159787456405000200000000000000)
      constant := (173346863842123642391761939142625892871572916036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree028.table
  base := (-6175097485912963965144150319583991324629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-5306412059848728285565977461508300000000000000)
      constant := (43492781888089611528575736107410831418491601078) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 28 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 28 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32365266845372149649/12500000000000000000)
  centralHi := (258922134762977197193/100000000000000000000)
  directionLo := (263673395922422197761/100000000000000000000)
  directionHi := (131836697961211098881/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree029.table
  base := (-6027499945591942986574697057394664546037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-21863171664116467502766427713083850000000000000)
      constant := (185078709551161630235667494737093415717968978136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree029.table
  base := (-6028108755793075276309692827750014684377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-5475315052059671612225688622824150000000000000)
      constant := (46436495556720432831703426228963516659411578414) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 29 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 29 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263673395922422197761/100000000000000000000)
  centralHi := (131836697961211098881/50000000000000000000)
  directionLo := (268340544018803645577/100000000000000000000)
  directionHi := (134170272009401822789/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree030.table
  base := (-11678798682834012021439133736070228345657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1609509)
      previous := (0)
      next := (1369995)
      square := (69347418263902081241312203090800000000000000)
      linear := (-2504163359431895649527266557907500000000000000)
      constant := (21911546470597398540595302859243446517936862972) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree030.table
  base := (-11679785801825661930837541700806533574743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (403161)
      previous := (0)
      next := (341715)
      square := (17336854565975520310328050772700000000000000)
      linear := (-627135338252290548765044420460000000000000000)
      constant := (5497655607323357809947841922451020164433943857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 30 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 30 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268340544018803645577/100000000000000000000)
  centralHi := (134170272009401822789/50000000000000000000)
  directionLo := (13646394708067822031/5000000000000000000)
  directionHi := (272927894161356440621/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree031.table
  base := (-2805276447219707599094219023161014224659/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-23211768805657654188724370329251150000000000000)
      constant := (209722131894209491871882744020154127477612868304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree031.table
  base := (-11221905165206511854383859234585744158079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-5813121036481558265545110945455850000000000000)
      constant := (52619907937152277152180380178355944843560009489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 31 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 31 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13646394708067822031/5000000000000000000)
  centralHi := (272927894161356440621/100000000000000000000)
  directionLo := (1083747674455254121/390625000000000000)
  directionHi := (277439404660545054977/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree032.table
  base := (-5341358209373507483031755653162679360369/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-23886067376428247531703341637334800000000000000)
      constant := (222633069949146369682317303930962185730409687032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree032.table
  base := (-10683363093246817920841166227711286069463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-5982024028692501592204822106771700000000000000)
      constant := (55859448506607281784487651185371015167098738233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 32 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 32 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1083747674455254121/390625000000000000)
  centralHi := (277439404660545054977/100000000000000000000)
  directionLo := (281878717013971729327/100000000000000000000)
  directionHi := (17617419813373233083/6250000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree033.table
  base := (-10064253854179353856754452155299592831691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35640000000000000000000000000000000000000000
      center := (146319)
      previous := (0)
      next := (124545)
      square := (6304310751263825567392018462800000000000000)
      linear := (-248084504517160008835174878236550000000000000)
      constant := (2383197095797484116942888390329407563647853276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree033.table
  base := (-10064776490034120753353923226111353326483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (36651)
      previous := (0)
      next := (31065)
      square := (1576077687815956391848004615700000000000000)
      linear := (-62130575968721665847116497657450000000000000)
      constant := (597954219775581578945711521240491034186103647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 33 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 33 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281878717013971729327/100000000000000000000)
  centralHi := (17617419813373233083/6250000000000000000)
  directionLo := (286249190308877278013/100000000000000000000)
  directionHi := (143124595154438639007/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree034.table
  base := (-9366206645852098707465000708954675975877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-25234664517969434217661284253502100000000000000)
      constant := (249632287120356759633665081034147061697375462828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree034.table
  base := (-2341657162321275376910636980990540498551/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-6319830013114388245524244429403400000000000000)
      constant := (62633923059822706017528806106283146652653259364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 34 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 34 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286249190308877278013/100000000000000000000)
  centralHi := (143124595154438639007/50000000000000000000)
  directionLo := (72638482741387212757/25000000000000000000)
  directionHi := (290553930965548851029/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree035.table
  base := (-8588957751104272411327566690868357914531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-25908963088740027560640255561585750000000000000)
      constant := (263720258737228194369753428188341045504368540084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree035.table
  base := (-4294649102578623154028989013911441535689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-6488733005325331572183955590719250000000000000)
      constant := (66168781013787273196654875831636740057156817998) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 35 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 35 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72638482741387212757/25000000000000000000)
  centralHi := (290553930965548851029/100000000000000000000)
  directionLo := (294795818570375949593/100000000000000000000)
  directionHi := (147397909285187974797/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree036.table
  base := (-3866403682001227702124599293667519919979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (536503)
      previous := (0)
      next := (456665)
      square := (23115806087967360413770734363600000000000000)
      linear := (-984565246648541514948860254432200000000000000)
      constant := (10303715607973761326330640472054930699371428856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree036.table
  base := (-1933270451008866059711113254235636390363/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (134387)
      previous := (0)
      next := (113905)
      square := (5778951521991840103442683590900000000000000)
      linear := (-246579111019862033290506176001300000000000000)
      constant := (2585259831585011533614501839209048703650736316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 36 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 36 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294795818570375949593/100000000000000000000)
  centralHi := (147397909285187974797/50000000000000000000)
  directionLo := (59795505681822977517/20000000000000000000)
  directionHi := (149488764204557443793/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree037.table
  base := (-1699497701508810621087440200479079317487/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-27257560230281214246598198177753050000000000000)
      constant := (293072392124654094122997254228878252717240627472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree037.table
  base := (-6798211861851406303200438090015926447391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-6826538989747218225503377913350950000000000000)
      constant := (73533605875669905646997694170594203894002087281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 37 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 37 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59795505681822977517/20000000000000000000)
  centralHi := (149488764204557443793/50000000000000000000)
  directionLo := (303101551201355922367/100000000000000000000)
  directionHi := (4735961737521186287/1562500000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree038.table
  base := (-5784692547617382552777758974109145239957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-27931858801051807589577169485836700000000000000)
      constant := (308336405777512550962677678502708869380114531948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree038.table
  base := (-2892435236847972284930317546735572959007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-6995441981958161552163089074666800000000000000)
      constant := (77363536219985185180562290052314828689717903074) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 38 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 38 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303101551201355922367/100000000000000000000)
  centralHi := (4735961737521186287/1562500000000000000)
  directionLo := (153585105224850231803/50000000000000000000)
  directionHi := (307170210449700463607/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree039.table
  base := (-469305719801393895848777609848208007911/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1609509)
      previous := (0)
      next := (1369995)
      square := (69347418263902081241312203090800000000000000)
      linear := (-3178461930202488992506237865991150000000000000)
      constant := (35999145705612475382019647369055931970078571560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree039.table
  base := (-4693200310252128454736636821763855737177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (403161)
      previous := (0)
      next := (341715)
      square := (17336854565975520310328050772700000000000000)
      linear := (-796038330463233875424755581775850000000000000)
      constant := (9032421544544763211373021290555561199919928223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 39 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 39 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153585105224850231803/50000000000000000000)
  centralHi := (307170210449700463607/100000000000000000000)
  directionLo := (311185677746837118137/100000000000000000000)
  directionHi := (155592838873418559069/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree040.table
  base := (-3523198119587821826368164266967703974433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-29280455942592994275535112102004000000000000000)
      constant := (340040068845330596792669591086552683200476958012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree040.table
  base := (-1761656577105123116193345623566584136311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-7333247966380048205482511397298500000000000000)
      constant := (85318369058183629173971890363266630359840286002) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 40 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 40 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311185677746837118137/100000000000000000000)
  centralHi := (155592838873418559069/50000000000000000000)
  directionLo := (157574993163416830983/50000000000000000000)
  directionHi := (315149986326833661967/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree041.table
  base := (-2275204180159555671882137549367749986327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-29954754513363587618514083410087650000000000000)
      constant := (356479646906201183438217994198324191503324326628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree041.table
  base := (-284412073505566355806819430408133022659/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-7502150958590991532142222558614350000000000000)
      constant := (89443253966264996381680514129401800703634178152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 41 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 41 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157574993163416830983/50000000000000000000)
  centralHi := (315149986326833661967/100000000000000000000)
  directionLo := (79766260775173817453/25000000000000000000)
  directionHi := (319065043100695269813/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree042.table
  base := (-949145046039726127150302169423778161369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1609509)
      previous := (0)
      next := (1369995)
      square := (69347418263902081241312203090800000000000000)
      linear := (-3403228120459353440165894968685700000000000000)
      constant := (41479002328037964064747458826584203950961689724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree042.table
  base := (-94921923361638164548148358166707299807/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (403161)
      previous := (0)
      next := (341715)
      square := (17336854565975520310328050772700000000000000)
      linear := (-852339327866881650977992635547800000000000000)
      constant := (10407382508009022038927509713799006017545915930) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 42 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 42 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79766260775173817453/25000000000000000000)
  centralHi := (319065043100695269813/100000000000000000000)
  directionLo := (161466319689195257493/50000000000000000000)
  directionHi := (322932639378390514987/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree043.table
  base := (454924668803457456030119232239964275703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-31303351654904774304472026026254950000000000000)
      constant := (390534171713977989111346271961726318472681943708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree043.table
  base := (909730285480123276887393543669200631/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-7839956943012878185461644881246050000000000000)
      constant := (97987930132957666948345286856880427009229939500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 43 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 43 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161466319689195257493/50000000000000000000)
  centralHi := (322932639378390514987/100000000000000000000)
  directionLo := (163377230224210483767/50000000000000000000)
  directionHi := (65350892089684193507/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree044.table
  base := (484240537551239937562729762298343144037/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320760000000000000000000000000000000000000000
      center := (1316871)
      previous := (0)
      next := (1120905)
      square := (56738796761374430106528166165200000000000000)
      linear := (-2907059111425033422495545212212600000000000000)
      constant := (37104462189521035147208547220609751618752523248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree044.table
  base := (484228603489767053357216802804436081831/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80190000000000000000000000000000000000000000
      center := (329859)
      previous := (0)
      next := (279585)
      square := (14184699190343607526632041541300000000000000)
      linear := (-728078175929438319283759640232900000000000000)
      constant := (9309792084809823738931963686817555091760811156) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 44 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 44 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163377230224210483767/50000000000000000000)
  centralHi := (65350892089684193507/20000000000000000000)
  directionLo := (165266047080142711101/50000000000000000000)
  directionHi := (330532094160285422203/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree045.table
  base := (874233458527788966545123050652495408453/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (536503)
      previous := (0)
      next := (456665)
      square := (23115806087967360413770734363600000000000000)
      linear := (-1209331436905405962608517357126750000000000000)
      constant := (15783546156370201641300672800911402552490655216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree045.table
  base := (1748447786171909659520443497009216327227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (134387)
      previous := (0)
      next := (113905)
      square := (5778951521991840103442683590900000000000000)
      linear := (-302880108423509808843743229773250000000000000)
      constant := (3960214372605794526075091911362114469482101218) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 45 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 45 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165266047080142711101/50000000000000000000)
  centralHi := (330532094160285422203/100000000000000000000)
  directionLo := (334267038633827721599/100000000000000000000)
  directionHi := (104458449573071163/31250000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree046.table
  base := (2567406703922180333582707015024851620993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-33326247367216554333408939950505900000000000000)
      constant := (444554148841710218485942462811231410843089372296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree046.table
  base := (641847844405627092162786460884139586193/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-8346665919645708165440778365193600000000000000)
      constant := (111542153233984408229163355852047457550067986696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 46 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 46 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334267038633827721599/100000000000000000000)
  centralHi := (104458449573071163/31250000000000000)
  directionLo := (337960709201637758527/100000000000000000000)
  directionHi := (5280636081275589977/1562500000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree047.table
  base := (171264506081564399287419787161747001993/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-34000545937987147676387911258589550000000000000)
      constant := (463344284665524599061325472000137222545308085920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree047.table
  base := (6850555698189591045236735085087996256297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-8515568911856651492100489526509450000000000000)
      constant := (116256806666283024222927902768381445811771702073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 47 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 47 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (337960709201637758527/100000000000000000000)
  centralHi := (5280636081275589977/1562500000000000000)
  directionLo := (170807222337873528521/50000000000000000000)
  directionHi := (341614444675747057043/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree048.table
  base := (8644218168485134760373898489021909977253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1609509)
      previous := (0)
      next := (1369995)
      square := (69347418263902081241312203090800000000000000)
      linear := (-3852760500973082335485209174074800000000000000)
      constant := (53614016443046322112557957800350814958748226612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree048.table
  base := (8644198522911100642018163456916262989963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (403161)
      previous := (0)
      next := (341715)
      square := (17336854565975520310328050772700000000000000)
      linear := (-964941322674177202084466743091700000000000000)
      constant := (13452194106294032848683761886912036293564627363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 48 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 48 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (170807222337873528521/50000000000000000000)
  centralHi := (341614444675747057043/100000000000000000000)
  directionLo := (345229513017302929589/100000000000000000000)
  directionHi := (34522951301730292959/10000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree049.table
  base := (2628928626256049042246324801714685573827/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-35349143079528334362345853874756850000000000000)
      constant := (502099734333960182521654299647478997134007293488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree049.table
  base := (525784939388637824359410162251601935293/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-8853374896278538145419911849141150000000000000)
      constant := (125980973007609882950371425820392299852205204740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 49 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 49 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345229513017302929589/100000000000000000000)
  centralHi := (34522951301730292959/10000000000000000000)
  directionLo := (174403558238650351091/50000000000000000000)
  directionHi := (348807116477300702183/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree050.table
  base := (6232529656485938350227150936330261534771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-36023441650298927705324825182840500000000000000)
      constant := (522065040197997111605719525916688142067764921112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree050.table
  base := (12465046743773613514322925517999434671841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-9022277888489481472079623010457000000000000000)
      constant := (130990483959224161796216420935820337132968422769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 50 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 50 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174403558238650351091/50000000000000000000)
  centralHi := (348807116477300702183/100000000000000000000)
  directionLo := (352348396267464661659/100000000000000000000)
  directionHi := (17617419813373233083/5000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree051.table
  base := (2898448959857154043097172163775086625729/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1609509)
      previous := (0)
      next := (1369995)
      square := (69347418263902081241312203090800000000000000)
      linear := (-4077526691229946783144866276769350000000000000)
      constant := (60269118092206863983628110253069828417875398580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree051.table
  base := (14492234751628456619161524311755917388649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (403161)
      previous := (0)
      next := (341715)
      square := (17336854565975520310328050772700000000000000)
      linear := (-1021242320077824977637703796863650000000000000)
      constant := (15122031015292824737395233432800938496326148849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 51 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 51 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352348396267464661659/100000000000000000000)
  centralHi := (17617419813373233083/5000000000000000000)
  directionLo := (44481804601590221317/12500000000000000000)
  directionHi := (355854436812721770537/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree052.table
  base := (16597264853930344945966796665074799339341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-37372038791840114391282767799007800000000000000)
      constant := (563170800073713678375520716970427006899695721076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree052.table
  base := (165972568250485987277462710791795716401/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-9360083872911368125399045333088700000000000000)
      constant := (141304358014799126673286728421143550834801580900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 52 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 52 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44481804601590221317/12500000000000000000)
  centralHi := (355854436812721770537/100000000000000000000)
  directionLo := (179663134815092546103/50000000000000000000)
  directionHi := (359326269630185092207/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree053.table
  base := (9390057343123546102841144134303513211649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-38046337362610707734261739107091450000000000000)
      constant := (584311250239236033603513407362395177212590773128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree053.table
  base := (18780108272900968036154408338546489280829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-9528986865122311452058756494404550000000000000)
      constant := (146608720176915116775653080998920266022972645261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 53 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 53 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179663134815092546103/50000000000000000000)
  centralHi := (359326269630185092207/100000000000000000000)
  directionLo := (72552975374794813007/20000000000000000000)
  directionHi := (90691219218493516259/25000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree054.table
  base := (5260197634974014178974242551392296192353/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (536503)
      previous := (0)
      next := (456665)
      square := (23115806087967360413770734363600000000000000)
      linear := (-1434097627162270410268174459821300000000000000)
      constant := (22438644888928032484292710816993509356566676016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree054.table
  base := (2630098177354789057531013179573498634943/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (134387)
      previous := (0)
      next := (113905)
      square := (5778951521991840103442683590900000000000000)
      linear := (-359181105827157584396980283545200000000000000)
      constant := (5630050566655425117946905360164607960322870248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 54 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 54 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72552975374794813007/20000000000000000000)
  centralHi := (90691219218493516259/25000000000000000000)
  directionLo := (366171194580396574271/100000000000000000000)
  directionHi := (5721424915318696473/1562500000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree055.table
  base := (5844822367347784665609245800319145988717/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320760000000000000000000000000000000000000000
      center := (1316871)
      previous := (0)
      next := (1120905)
      square := (56738796761374430106528166165200000000000000)
      linear := (-3581357682195626765474516520296250000000000000)
      constant := (57069753119991152298059656658970280519436345968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree055.table
  base := (11689642690814026462697681416899767335749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80190000000000000000000000000000000000000000
      center := (329859)
      previous := (0)
      next := (279585)
      square := (14184699190343607526632041541300000000000000)
      linear := (-896981168140381645943470801548750000000000000)
      constant := (14319299375362960575675691413666894718530742462) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 55 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 55 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366171194580396574271/100000000000000000000)
  centralHi := (5721424915318696473/1562500000000000000)
  directionLo := (18477305782193986819/5000000000000000000)
  directionHi := (369546115643879736381/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree056.table
  base := (25795609164920090236684197413339936128873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-40069233074922487763198653031342400000000000000)
      constant := (650082866380788513943970914470870909703967033828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree056.table
  base := (12897802951519290067739913994638101912263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-10035695841755141432037889978352100000000000000)
      constant := (163111503465607029194850436135313864663157613934) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 56 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 56 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18477305782193986819/5000000000000000000)
  centralHi := (369546115643879736381/100000000000000000000)
  directionLo := (372890492550460210483/100000000000000000000)
  directionHi := (93222623137615052621/25000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree057.table
  base := (5657949563003190745295778282210999920541/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1609509)
      previous := (0)
      next := (1369995)
      square := (69347418263902081241312203090800000000000000)
      linear := (-4527059071743675678464180482158450000000000000)
      constant := (74754461949395959731168853139410473641924446820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree057.table
  base := (14144872606493435006200269436565288625781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (403161)
      previous := (0)
      next := (341715)
      square := (17336854565975520310328050772700000000000000)
      linear := (-1133844314885120528744177904407550000000000000)
      constant := (18756555128155845922323858746631571537642559162) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 57 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 57 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (372890492550460210483/100000000000000000000)
  centralHi := (93222623137615052621/25000000000000000000)
  directionLo := (376205139892545736909/100000000000000000000)
  directionHi := (37620513989254573691/10000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree058.table
  base := (30861703998901099364298154235275790379801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-41417830216463674449156595647509700000000000000)
      constant := (695889157309926550411648800788961912524447465636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree058.table
  base := (15430850961940203281624995450599637365869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-10373501826177028085357312300983800000000000000)
      constant := (174604771069981170407407105231582211824811877242) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 58 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 58 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376205139892545736909/100000000000000000000)
  centralHi := (37620513989254573691/10000000000000000000)
  directionLo := (379490836685966626957/100000000000000000000)
  directionHi := (189745418342983313479/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree059.table
  base := (33511476602092297408257393502264957468169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-42092128787234267792135566955593350000000000000)
      constant := (719379865283647447588150690035365506970738877284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree059.table
  base := (16755737473916453998888229929968637526761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-10542404818387971412017023462299650000000000000)
      constant := (180498828119381339483891251329855475845196122098) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 59 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 59 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (379490836685966626957/100000000000000000000)
  centralHi := (189745418342983313479/50000000000000000000)
  directionLo := (2990221316468670339/781250000000000000)
  directionHi := (382748328507989803393/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree060.table
  base := (4529883093780082750861261670887964337173/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1609509)
      previous := (0)
      next := (1369995)
      square := (69347418263902081241312203090800000000000000)
      linear := (-4751825262000540126123837584853000000000000000)
      constant := (82584697906358285069081922934360809030996242336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree060.table
  base := (36239063431801738657697023763277203761853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (403161)
      previous := (0)
      next := (341715)
      square := (17336854565975520310328050772700000000000000)
      linear := (-1190145312288768304297414958179500000000000000)
      constant := (20721240802928564742398409861003879874069921253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 60 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 60 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2990221316468670339/781250000000000000)
  centralHi := (382748328507989803393/100000000000000000000)
  directionLo := (48247291184114867579/12500000000000000000)
  directionHi := (385978329472918940633/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree061.table
  base := (9761116939316587529710197592616910098217/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-43440725928775454478093509571760650000000000000)
      constant := (767536404688584237013068953605473043803157973648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree061.table
  base := (39044466706767019721694160207774955843993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-10880210802809858065336445784931350000000000000)
      constant := (192581788331894825509540820155435139830042778537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 61 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 61 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48247291184114867579/12500000000000000000)
  centralHi := (385978329472918940633/100000000000000000000)
  directionLo := (389181524060110351279/100000000000000000000)
  directionHi := (4864769050751379391/1250000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree062.table
  base := (41927685084699272494408633422602202065479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-44115024499546047821072480879844300000000000000)
      constant := (792202235687734829351638182128938164317975348444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree062.table
  base := (8385536849582493133905128067901112719479/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-11049113795020801391996156946247200000000000000)
      constant := (198770691389701048238301598784080271259362615555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 62 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 62 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (389181524060110351279/100000000000000000000)
  centralHi := (4864769050751379391/1250000000000000000)
  directionLo := (392358568807660091281/100000000000000000000)
  directionHi := (196179284403830045641/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree063.table
  base := (8977743261960896684884746391637434238889/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (536503)
      previous := (0)
      next := (456665)
      square := (23115806087967360413770734363600000000000000)
      linear := (-1658863817419134857927831562515850000000000000)
      constant := (30268880518722971679007567573042122765669007260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree063.table
  base := (4488871564342612453310018814087112418909/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (134387)
      previous := (0)
      next := (113905)
      square := (5778951521991840103442683590900000000000000)
      linear := (-415482103230805359950217337317150000000000000)
      constant := (7594736161609267792470913380323482212725757030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 63 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 63 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (392358568807660091281/100000000000000000000)
  centralHi := (196179284403830045641/50000000000000000000)
  directionLo := (197755046941816648321/50000000000000000000)
  directionHi := (395510093883633296643/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree064.table
  base := (47927561100594112508172774601463804244661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-45463621641087234507030423496011600000000000000)
      constant := (842709019524803182717061298702493282834469208596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree064.table
  base := (23963780285027430726619426670310064690673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-11386919779442688045315579268878900000000000000)
      constant := (211443343224628536211986691584919560992599149314) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 64 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 64 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (197755046941816648321/50000000000000000000)
  centralHi := (395510093883633296643/100000000000000000000)
  directionLo := (19931835227274325839/5000000000000000000)
  directionHi := (398636704545486516781/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree065.table
  base := (51044219196237846569796740384968326267279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-46137920211857827850009394804095250000000000000)
      constant := (868549972153553347123491711297930020304341653244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree065.table
  base := (12761054693487611503660612100959910378059/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-11555822771653631371975290430194750000000000000)
      constant := (217927091950844267127414563699369759688152825324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 65 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 65 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19931835227274325839/5000000000000000000)
  centralHi := (398636704545486516781/100000000000000000000)
  directionLo := (401738982497256042237/100000000000000000000)
  directionHi := (200869491248628021119/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree066.table
  base := (27119345195852745584851207044296900104061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35640000000000000000000000000000000000000000
      center := (146319)
      previous := (0)
      next := (124545)
      square := (6304310751263825567392018462800000000000000)
      linear := (-472850694774024456494831980931100000000000000)
      constant := (9038208402216451463305123743162079553941746808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree066.table
  base := (27119345027830827212902162956243876683089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8910000000000000000000000000000000000000000
      center := (36651)
      previous := (0)
      next := (31065)
      square := (1576077687815956391848004615700000000000000)
      linear := (-118431573372369441400353551429400000000000000)
      constant := (2267768914388929597409830987373601588249264598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 66 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 66 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (401738982497256042237/100000000000000000000)
  centralHi := (200869491248628021119/50000000000000000000)
  directionLo := (404817487153131371187/100000000000000000000)
  directionHi := (101204371788282842797/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree067.table
  base := (14377743631431797151390043602476998026779/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-47486517353399014535967337420262550000000000000)
      constant := (921406998465527414435948742265975869740606380976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree067.table
  base := (28755487129187407584199604224525084756531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-11893628756075518025294712752826450000000000000)
      constant := (231189434931775448109502849341048435152577685958) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 67 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 67 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (404817487153131371187/100000000000000000000)
  centralHi := (101204371788282842797/25000000000000000000)
  directionLo := (407872756815187117071/100000000000000000000)
  directionHi := (25492047300949194817/6250000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree068.table
  base := (15215267867838613678852783147570395852523/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-48160815924169607878946308728346200000000000000)
      constant := (948423072047057510471947259902680267764083220912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree068.table
  base := (7607633907337443581427431919299309667751/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-12062531748286461351954423914142300000000000000)
      constant := (237968029161774379031860115497653982451861183672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 68 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 68 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (407872756815187117071/100000000000000000000)
  centralHi := (25492047300949194817/6250000000000000000)
  directionLo := (410905309772295172951/100000000000000000000)
  directionHi := (51363163721536896619/12500000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree069.table
  base := (8036122641070011034633072142907256573637/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1609509)
      previous := (0)
      next := (1369995)
      square := (69347418263902081241312203090800000000000000)
      linear := (-5426123832771133469102808892936650000000000000)
      constant := (108425650280969531711641102400569299631202919584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree069.table
  base := (64288980959448702763616748524528015534117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (403161)
      previous := (0)
      next := (341715)
      square := (17336854565975520310328050772700000000000000)
      linear := (-1359048304499711630957126119495350000000000000)
      constant := (27204989467325337934451551480907567830249880717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 69 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 69 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (410905309772295172951/100000000000000000000)
  centralHi := (51363163721536896619/12500000000000000000)
  directionLo := (82783129065314012461/20000000000000000000)
  directionHi := (206957822663285031153/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree070.table
  base := (1059292240913069212484036209838835593749/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-49509413065710794564904251344513500000000000000)
      constant := (1003630339882690776219491746996950349065585418496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree070.table
  base := (2711788131359231011461295729105282808779/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-12400337732708348005273846236774000000000000000)
      constant := (251820063057475964974926369828991822281989670275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 70 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 70 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82783129065314012461/20000000000000000000)
  centralHi := (206957822663285031153/50000000000000000000)
  directionLo := (41690424475310397967/10000000000000000000)
  directionHi := (416904244753103979671/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree071.table
  base := (17844559569661657722578157235170955909033/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-50183711636481387907883222652597150000000000000)
      constant := (1031821534086957798888984011041345028533978270352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree071.table
  base := (71378238171766577235113017780172716754487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-12569240724919291331933557398089850000000000000)
      constant := (258893502711078930495264762137292273922196543783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 71 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 71 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41690424475310397967/10000000000000000000)
  centralHi := (416904244753103979671/100000000000000000000)
  directionLo := (419871572198215288109/100000000000000000000)
  directionHi := (41987157219821528811/10000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree072.table
  base := (15007917131971643879787998281196295044537/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (536503)
      previous := (0)
      next := (456665)
      square := (23115806087967360413770734363600000000000000)
      linear := (-1883630007675999305587488665210400000000000000)
      constant := (39274238337930391891010261036897265918210047580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree072.table
  base := (2344987049216097488941878153816095879603/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (134387)
      previous := (0)
      next := (113905)
      square := (5778951521991840103442683590900000000000000)
      linear := (-471783100634453135503454391089100000000000000)
      constant := (9854267561574537841689725841157149927637216032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 72 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 72 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (419871572198215288109/100000000000000000000)
  centralHi := (41987157219821528811/10000000000000000000)
  directionLo := (422818075520957593991/100000000000000000000)
  directionHi := (52852259440119699249/12500000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree073.table
  base := (78778745522946729334852930938683535476439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-51532308778022574593841165268764450000000000000)
      constant := (1089379042980374602712887780805237354860864831004) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree073.table
  base := (78778745455451080931036927260286228862363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-12907046709341177985252979720721550000000000000)
      constant := (273335227408426973523993113062727756711720177867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 73 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 73 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (422818075520957593991/100000000000000000000)
  centralHi := (52852259440119699249/12500000000000000000)
  directionLo := (42574418708220936257/10000000000000000000)
  directionHi := (425744187082209362571/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree074.table
  base := (82595717836803034169741590164051910291347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-52206607348793167936820136576848100000000000000)
      constant := (1118745357644743444088073472631705463569557710092) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree074.table
  base := (20648929445795291250642700295316943870719/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-13075949701552121311912690882037400000000000000)
      constant := (280703512446158965435817599344382374207569009084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 74 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 74 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42574418708220936257/10000000000000000000)
  centralHi := (425744187082209362571/100000000000000000000)
  directionLo := (428650324485280626239/100000000000000000000)
  directionHi := (1339532264016501957/312500000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree075.table
  base := (8649050257661395813768946044488655555527/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1609509)
      previous := (0)
      next := (1369995)
      square := (69347418263902081241312203090800000000000000)
      linear := (-5875656213284862364422123098325750000000000000)
      constant := (127611486567608013722032356248235043461488805080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree075.table
  base := (86490502534021881224254856534870595869139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (403161)
      previous := (0)
      next := (341715)
      square := (17336854565975520310328050772700000000000000)
      linear := (-1471650299307007182063600227039250000000000000)
      constant := (32018897697064901870615798508884985460113431339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 75 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 75 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (428650324485280626239/100000000000000000000)
  centralHi := (1339532264016501957/312500000000000000)
  directionLo := (215768445635814330993/50000000000000000000)
  directionHi := (431536891271628661987/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree076.table
  base := (45231549861256962818293365377473292120077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-53555204490334354622778079193015400000000000000)
      constant := (1178653107364551350710394964329212407996958976744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree076.table
  base := (1130788746108610910557208874464179869853/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-13413755685974007965232113204669100000000000000)
      constant := (295734927889001373898472718945323667371189062160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 76 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 76 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215768445635814330993/50000000000000000000)
  centralHi := (431536891271628661987/100000000000000000000)
  directionLo := (434404277574964199127/100000000000000000000)
  directionHi := (54300534696870524891/12500000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree077.table
  base := (18902701851705499620821463629853840681191/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320760000000000000000000000000000000000000000
      center := (1316871)
      previous := (0)
      next := (1120905)
      square := (56738796761374430106528166165200000000000000)
      linear := (-4929954823736813451432459136463550000000000000)
      constant := (109926776582485855989437078283184329280949412580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree077.table
  base := (1890270184633390836443412795633155648847/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80190000000000000000000000000000000000000000
      center := (329859)
      previous := (0)
      next := (279585)
      square := (14184699190343607526632041541300000000000000)
      linear := (-1234787152562268299262893124180450000000000000)
      constant := (27581641662822035078543487954362470007405204650) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 77 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 77 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (434404277574964199127/100000000000000000000)
  centralHi := (54300534696870524891/12500000000000000000)
  directionLo := (218626430368374965767/50000000000000000000)
  directionHi := (87450572147349986307/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree078.table
  base := (246604327929349913792693512147995780943/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1609509)
      previous := (0)
      next := (1369995)
      square := (69347418263902081241312203090800000000000000)
      linear := (-6100422403541726812081780201020300000000000000)
      constant := (137791964914699393821421482158371054388435748800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree078.table
  base := (49320865575208829134600694120844138074237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (403161)
      previous := (0)
      next := (341715)
      square := (17336854565975520310328050772700000000000000)
      linear := (-1527951296710654957616837280811200000000000000)
      constant := (34573274497622273593320341331734211794531193674) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 78 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 78 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218626430368374965767/50000000000000000000)
  centralHi := (87450572147349986307/20000000000000000000)
  directionLo := (4400830058858404907/1000000000000000000)
  directionHi := (440083005885840490701/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree079.table
  base := (102847765451646735344686760952472323613353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-55578100202646134651714993117266350000000000000)
      constant := (1271452532835695337827150440971768560711941019108) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree079.table
  base := (51423882717360957777068104125508307819909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-13920464662606837945211246688616650000000000000)
      constant := (319019164450774874179525960320458443398972705962) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 79 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 79 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4400830058858404907/1000000000000000000)
  centralHi := (440083005885840490701/100000000000000000000)
  directionLo := (442895066484784635023/100000000000000000000)
  directionHi := (27680941655299039689/6250000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree080.table
  base := (53565806044821452057570063872389888094873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-56252398773416727994693964425350000000000000000)
      constant := (1303169088214510676465504813861177117111685219656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree080.table
  base := (26782903019052697855770860591404725955647/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-14089367654817781271870957849932500000000000000)
      constant := (326977140206827177776413503291058877887286664892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 80 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 80 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (442895066484784635023/100000000000000000000)
  centralHi := (27680941655299039689/6250000000000000000)
  directionLo := (445689384845103628799/100000000000000000000)
  directionHi := (34819483191023721/7812500000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree081.table
  base := (111493271078622739564318518468520946531567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (536503)
      previous := (0)
      next := (456665)
      square := (23115806087967360413770734363600000000000000)
      linear := (-2108396197932863753247145767904950000000000000)
      constant := (49454716680230866746619028565867864541774517556) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree081.table
  base := (111493271067964223429046645163272506333153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (134387)
      previous := (0)
      next := (113905)
      square := (5778951521991840103442683590900000000000000)
      linear := (-528084098038100911056691444861050000000000000)
      constant := (12408644360968405975635503386783717528190410851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 81 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 81 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (445689384845103628799/100000000000000000000)
  centralHi := (34819483191023721/7812500000000000)
  directionLo := (448466292613672331377/100000000000000000000)
  directionHi := (224233146306836165689/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree082.table
  base := (28983185603166335374599490412377178500719/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-57600995914957914680651907041517300000000000000)
      constant := (1367777319288774408165989238424467950363918756336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree082.table
  base := (14491592800526123865329494739848069335443/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-14427173639239667925190380172564200000000000000)
      constant := (343187937068224974856499194728472391784080732696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 82 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 82 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (448466292613672331377/100000000000000000000)
  centralHi := (224233146306836165689/50000000000000000000)
  directionLo := (56403263904019921253/12500000000000000000)
  directionHi := (18049044449286374801/4000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree083.table
  base := (30112506521696969132673972623024816528741/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-58275294485728508023630878349600950000000000000)
      constant := (1400668994980375571486507685161376160096439437904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree083.table
  base := (120450026080079697751177111508280879661157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-14596076631450611251850091333880050000000000000)
      constant := (351440758172632046590204068541847116864030997813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 83 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 83 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56403263904019921253/12500000000000000000)
  centralHi := (18049044449286374801/4000000000000000000)
  directionLo := (226984576185664070383/50000000000000000000)
  directionHi := (453969152371328140767/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree084.table
  base := (125045122096751801091907121993863797977779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1609509)
      previous := (0)
      next := (1369995)
      square := (69347418263902081241312203090800000000000000)
      linear := (-6549954784055455707401094406409400000000000000)
      constant := (159328041937726820151272194215479111335920847916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree084.table
  base := (7815320130714448053175097430408542584947/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (403161)
      previous := (0)
      next := (341715)
      square := (17336854565975520310328050772700000000000000)
      linear := (-1640553291517950508723311388355100000000000000)
      constant := (39976873451000281644007159135219146014001048752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 84 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 84 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226984576185664070383/50000000000000000000)
  centralHi := (453969152371328140767/100000000000000000000)
  directionLo := (228347859170929842437/50000000000000000000)
  directionHi := (3653565746734877479/800000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree085.table
  base := (129718030438910637929326614552698095947391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-59623891627269694709588820965768250000000000000)
      constant := (1467627466664985229342879990699555433819193650876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree085.table
  base := (32429507608672786133280448254663225836179/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-14933882615872497905169513656511750000000000000)
      constant := (368241245727021334019227312145806572701134053644) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 85 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 85 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228347859170929842437/50000000000000000000)
  centralHi := (3653565746734877479/800000000000000000)
  directionLo := (229703051241615159513/50000000000000000000)
  directionHi := (459406102483230319027/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree086.table
  base := (67234375555045170674784756413947392750899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-60298190198040288052567792273851900000000000000)
      constant := (1501694262655587197844527274623112628287312399128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree086.table
  base := (67234375553372281072287348547204274439317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-15102785608083441231829224817827600000000000000)
      constant := (376788912176413667698084559357637108688035426506) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 86 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 86 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229703051241615159513/50000000000000000000)
  centralHi := (459406102483230319027/100000000000000000000)
  directionLo := (462100589532060005139/100000000000000000000)
  directionHi := (23105029476603000257/5000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree087.table
  base := (8706080256718451426226750849608345085813/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1609509)
      previous := (0)
      next := (1369995)
      square := (69347418263902081241312203090800000000000000)
      linear := (-6774720974312320155060751509103950000000000000)
      constant := (170683640601151207478573250939003702409407405632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree087.table
  base := (69648642052421299912971229247320541022353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (403161)
      previous := (0)
      next := (341715)
      square := (17336854565975520310328050772700000000000000)
      linear := (-1696854288921598284276548442127050000000000000)
      constant := (42826095600770785000584047757682245995120163506) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 87 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 87 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462100589532060005139/100000000000000000000)
  centralHi := (23105029476603000257/5000000000000000000)
  directionLo := (232389727985620359961/50000000000000000000)
  directionHi := (464779455971240719923/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree088.table
  base := (72101814714316963268466135297021326286903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320760000000000000000000000000000000000000000
      center := (1316871)
      previous := (0)
      next := (1120905)
      square := (56738796761374430106528166165200000000000000)
      linear := (-5604253394507406794411430444547200000000000000)
      constant := (142818452266220654337710946173606812123957401256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree088.table
  base := (72101814713265567039150664474107823512637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80190000000000000000000000000000000000000000
      center := (329859)
      previous := (0)
      next := (279585)
      square := (14184699190343607526632041541300000000000000)
      linear := (-1403690144773211625922604285496300000000000000)
      constant := (35834462765306822741911487147187941273495672206) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 88 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 88 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232389727985620359961/50000000000000000000)
  centralHi := (464779455971240719923/100000000000000000000)
  directionLo := (467442970361056533671/100000000000000000000)
  directionHi := (58430371295132066709/12500000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree089.table
  base := (149187787071261134607673106720216951938637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-62321085910352068081504706198102850000000000000)
      constant := (1606244891208993960083130668184745629391720924532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree089.table
  base := (149187787069594420094457187083717921588407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-15609494584716271211808358301775150000000000000)
      constant := (403021602210532174531696559505367442895391793063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 89 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 89 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (467442970361056533671/100000000000000000000)
  centralHi := (58430371295132066709/12500000000000000000)
  directionLo := (58761424206677231123/12500000000000000000)
  directionHi := (94018278730683569797/20000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree090.table
  base := (154249757033331614398446077648325218662003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (536503)
      previous := (0)
      next := (456665)
      square := (23115806087967360413770734363600000000000000)
      linear := (-2333162388189728200906802870599500000000000000)
      constant := (60810315342642204544838894398472845207475055204) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree090.table
  base := (154249757032010710560058860883022197440187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (134387)
      previous := (0)
      next := (113905)
      square := (5778951521991840103442683590900000000000000)
      linear := (-584385095441748686609928498633000000000000000)
      constant := (15257866510490003770682052960944208519037090929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 90 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 90 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58761424206677231123/12500000000000000000)
  centralHi := (94018278730683569797/20000000000000000000)
  directionLo := (472724979490250492949/100000000000000000000)
  directionHi := (9454499589805009859/2000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree091.table
  base := (159389539312963952001546424965711638183669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-63669683051893254767462648814270150000000000000)
      constant := (1677903844054800055039839933492450680007673035284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree091.table
  base := (79694769655958619549335566952073460061863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-15947300569138157865127780624406850000000000000)
      constant := (421001471136304519231883995932315164427193746734) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 91 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 91 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (472724979490250492949/100000000000000000000)
  centralHi := (9454499589805009859/2000000000000000000)
  directionLo := (475343974487005394407/100000000000000000000)
  directionHi := (59417996810875674301/12500000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree092.table
  base := (164607133908411889127691655007344050531387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-64343981622663848110441620122353800000000000000)
      constant := (1714320880618759414280942744451001920413292463532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree092.table
  base := (32921426781516510244308226508463764478601/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-16116203561349101191787491785722700000000000000)
      constant := (430138828269602696933103855238028601004464578045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 92 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 92 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (475343974487005394407/100000000000000000000)
  centralHi := (59417996810875674301/12500000000000000000)
  directionLo := (477948618502185778013/100000000000000000000)
  directionHi := (238974309251092889007/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree093.table
  base := (42475635204510407562610477916895953422169/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1609509)
      previous := (0)
      next := (1369995)
      square := (69347418263902081241312203090800000000000000)
      linear := (-7224253354826049050380065714493050000000000000)
      constant := (194569958215849015395065738729503491769350853904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree093.table
  base := (169902540817384601837742117364919056302713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (403161)
      previous := (0)
      next := (341715)
      square := (17336854565975520310328050772700000000000000)
      linear := (-1809456283728893835383022549670950000000000000)
      constant := (48819385242553506215183272344891340420822890113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 93 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 93 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (477948618502185778013/100000000000000000000)
  centralHi := (238974309251092889007/50000000000000000000)
  directionLo := (480539144893725601173/100000000000000000000)
  directionHi := (240269572446862800587/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree094.table
  base := (35055152008062767847284495819723037237987/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-65692578764205034796399562738521100000000000000)
      constant := (1788330074025902094659831244595159281584511905660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree094.table
  base := (87637880019896690084168949215543031994921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-16454009545770987845106914108354400000000000000)
      constant := (448708387876306135521721601151802095618479972978) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 94 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 94 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (480539144893725601173/100000000000000000000)
  centralHi := (240269572446862800587/50000000000000000000)
  directionLo := (483115780762994838459/100000000000000000000)
  directionHi := (24155789038149741923/5000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree095.table
  base := (90363395786884660492132306537026897297949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-66366877334975628139378534046604750000000000000)
      constant := (1825922230868027426030874990302024930607538266728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree095.table
  base := (3614535831467141814530141000995324087939/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-16622912537981931171766625269670250000000000000)
      constant := (458140590349448374260223274242586545873650562550) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 95 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 95 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483115780762994838459/100000000000000000000)
  centralHi := (24155789038149741923/5000000000000000000)
  directionLo := (485678747187153722299/100000000000000000000)
  directionHi := (4856787471871537223/1000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree096.table
  base := (93127817708508800104728583269960163369613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1609509)
      previous := (0)
      next := (1369995)
      square := (69347418263902081241312203090800000000000000)
      linear := (-7449019545082913498039722817187600000000000000)
      constant := (207100677163169613659026345622687836489484616104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree096.table
  base := (186255635416691128886955330105765128366551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (403161)
      previous := (0)
      next := (341715)
      square := (17336854565975520310328050772700000000000000)
      linear := (-1865757281132541610936259603442900000000000000)
      constant := (51963452733587348618084654508181804023120566351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 96 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 96 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (485678747187153722299/100000000000000000000)
  centralHi := (4856787471871537223/1000000000000000000)
  directionLo := (244114129720264382847/50000000000000000000)
  directionHi := (97645651888105753139/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree097.table
  base := (191862291568727779344889956766704685797099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-67715474476516814825336476662772050000000000000)
      constant := (1902281664826929796786928717068106650455405222764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree097.table
  base := (38372458313693850803704911114012106187263/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-16960718522403817825086047592301950000000000000)
      constant := (477299840634702439069503617978144138123361409835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 97 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 97 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell187.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244114129720264382847/50000000000000000000)
  centralHi := (97645651888105753139/20000000000000000000)
  directionLo := (490764527205637950359/100000000000000000000)
  directionHi := (12269113180140948759/2500000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree098.table
  base := (197546760027621190684842365834187733379329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (14485581)
      previous := (0)
      next := (12329955)
      square := (624126764375118731171809827817200000000000000)
      linear := (-68389773047287408168315447970855700000000000000)
      constant := (1941048941942786087599334169749274856844628927044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree098.table
  base := (98773380013708246011821252508561300617549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882090000000000000000000000000000000000000000
      center := (3628449)
      previous := (0)
      next := (3075435)
      square := (156031691093779682792952456954300000000000000)
      linear := (-17129621514614761151745758753617800000000000000)
      constant := (487026888446584814590275708376385692532346759482) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 98 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 98 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell187.Kernel098
