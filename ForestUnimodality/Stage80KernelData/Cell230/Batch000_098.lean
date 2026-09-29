import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell230.Parameters
import ForestUnimodality.BinomialMassData.Q2_3.Batch000_049
import ForestUnimodality.BinomialMassData.Q2_3.Batch050_099
import ForestUnimodality.BinomialMassData.Q35_52.Batch000_049
import ForestUnimodality.BinomialMassData.Q35_52.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree000.table
  base := (96581684674990243366465847/20000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (2)
      previous := (0)
      next := (1)
      square := (128327411949569536453452656000000000000)
      linear := (-213524120551405266477118520000000000000)
      constant := (9658168467499024336646584700000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree000.table
  base := (96581684674990243366465847/20000000000000000000000000)
  polynomial :=
    { denominator := 104000000000000000000000000000000000000000
      center := (105)
      previous := (0)
      next := (51)
      square := (6673025421377615895579538112000000000000)
      linear := (-11103254268673073856810163040000000000000)
      constant := (502224760309949265505622404400000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree001.table
  base := (36745178896423464981069302453864924391847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-17308230141787409178677492760000000000000)
      constant := (339678881923344733553006330804784319526623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree001.table
  base := (7326822782288538772765342442311446416831/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (1365)
      previous := (0)
      next := (663)
      square := (86749330477909006642533995456000000000000)
      linear := (-261120250366858238311174036480000000000000)
      constant := (5089385945587497277175330293502537777777756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (29863125692764953999/100000000000000000000)
  directionHi := (14931562846382477/50000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree002.table
  base := (27509643441297622563544228592255826758711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-25007874858761581365884652120000000000000)
      constant := (270664431160728481976801381010302440828399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree002.table
  base := (27332153051837967181950781493491033859303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-1889490976204832582419079767200000000000000)
      constant := (20234075609742473188247015073599938888888828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29863125692764953999/100000000000000000000)
  centralHi := (14931562846382477/50000000000000000)
  directionLo := (21116418684780313781/50000000000000000000)
  directionHi := (42232837369560627563/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree003.table
  base := (10061118836287011671913865550255917159763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (10)
      previous := (0)
      next := (5)
      square := (641637059747847682267263280000000000000)
      linear := (-3634168841748417061454645720000000000000)
      constant := (24824027117079466737667969420511834319526) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree003.table
  base := (4977376274572660830582118073864790765817/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-2473380700575373973282289352000000000000000)
      constant := (16684639715137821003849525586230394230769168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21116418684780313781/50000000000000000000)
  centralHi := (42232837369560627563/100000000000000000000)
  directionLo := (12931112743171106689/25000000000000000000)
  directionHi := (51724450972684426757/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree004.table
  base := (7106678271511261550137996204118211702827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-40407164292709925740298970840000000000000)
      constant := (194607875177233591544843003994127810650886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree004.table
  base := (3496678578097513846618584818304846922881/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-3057270424945915364145498936800000000000000)
      constant := (14542109964957919009308021952696306079470224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12931112743171106689/25000000000000000000)
  centralHi := (51724450972684426757/100000000000000000000)
  directionLo := (59726251385529907999/100000000000000000000)
  directionHi := (14931562846382477/25000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree005.table
  base := (9490144340925135272424865564346946522991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-48106809009684097927506130200000000000000)
      constant := (181603623125821775650117896079122518706919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree005.table
  base := (9263774189014561228133673579882196866523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-3641160149316456755008708521600000000000000)
      constant := (13603681961740537113754320992500365081769548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59726251385529907999/100000000000000000000)
  centralHi := (14931562846382477/25000000000000000)
  directionLo := (267103916278571747/400000000000000000)
  directionHi := (66775979069642936751/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree006.table
  base := (1432198856534634120118941427161864481/2500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (2)
      previous := (0)
      next := (1)
      square := (128327411949569536453452656000000000000)
      linear := (-1240143416147961558104739768000000000000)
      constant := (4053094158626440945258869717729491584800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree006.table
  base := (86120950899168606370900434802648047267/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-4225049873686998145871918106400000000000000)
      constant := (13714589648948333170439881871301765116959488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267103916278571747/400000000000000000)
  centralHi := (66775979069642936751/100000000000000000000)
  directionLo := (2925976802874901777/4000000000000000000)
  directionHi := (36574710035936272213/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree007.table
  base := (545403700291435702694498241024092904043/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18000000000000000000000000000000000000000
      center := (18)
      previous := (0)
      next := (9)
      square := (1154946707546125828081073904000000000000)
      linear := (-12701219688726488460384089784000000000000)
      constant := (39028819107897571661166182585216836136387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree007.table
  base := (252467723979288991474034343492872047589/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (1365)
      previous := (0)
      next := (663)
      square := (86749330477909006642533995456000000000000)
      linear := (-961787919611507907347025538240000000000000)
      constant := (2947123912344452346607140837702363008340328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2925976802874901777/4000000000000000000)
  centralHi := (36574710035936272213/50000000000000000000)
  directionLo := (79010403954119537181/100000000000000000000)
  directionHi := (39505201977059768591/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree008.table
  base := (333687373517404408920392901897128347661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-71205743160606614489127608280000000000000)
      constant := (218508062589442910295211380597074155128949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree008.table
  base := (14891146645862698161779093950280338921/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (1365)
      previous := (0)
      next := (663)
      square := (86749330477909006642533995456000000000000)
      linear := (-1078565864485616185519667455200000000000000)
      constant := (3312577903283884452379108805420779018221192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79010403954119537181/100000000000000000000)
  centralHi := (39505201977059768591/50000000000000000000)
  directionLo := (21116418684780313781/25000000000000000000)
  directionHi := (675725397912970041/800000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree009.table
  base := (-786094954954829474806567891007394567839/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (10)
      previous := (0)
      next := (5)
      square := (641637059747847682267263280000000000000)
      linear := (-8767265319731198519592751960000000000000)
      constant := (27932467857555015606321897897985210864322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree009.table
  base := (-1738288909704467079054268803257144939057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-5976719046798622318461546860800000000000000)
      constant := (19113432378699849653920615725498170021197468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21116418684780313781/25000000000000000000)
  centralHi := (675725397912970041/800000000000000000)
  directionLo := (44794688539147430999/50000000000000000000)
  directionHi := (89589377078294861999/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree010.table
  base := (-617488700704785805981806896250764668709/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18000000000000000000000000000000000000000
      center := (18)
      previous := (0)
      next := (9)
      square := (1154946707546125828081073904000000000000)
      linear := (-17321006518910991772708385400000000000000)
      constant := (58585013706569058316171911533743117981619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree010.table
  base := (-808727543037699300602795970860322079349/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-6560608771169163709324756445600000000000000)
      constant := (22321009420948366172959423974793689097440304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44794688539147430999/50000000000000000000)
  centralHi := (89589377078294861999/100000000000000000000)
  directionLo := (94435495241030970819/100000000000000000000)
  directionHi := (4721774762051548541/5000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree011.table
  base := (-2144777087070649225781482867106713107767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-94304677311529131050749086360000000000000)
      constant := (342409309132650330090737847512079164060194) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree011.table
  base := (-2209584715625506103064973242265675864063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-7144498495539705100187966030400000000000000)
      constant := (26132745876554413218262322058956806231786824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94435495241030970819/100000000000000000000)
  centralHi := (4721774762051548541/5000000000000000000)
  directionLo := (99044782990123520443/100000000000000000000)
  directionHi := (24761195747530880111/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree012.table
  base := (-655064352250399873677312237230417908169/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (10)
      previous := (0)
      next := (5)
      square := (641637059747847682267263280000000000000)
      linear := (-11333813558722589248661805080000000000000)
      constant := (44365221827915263334771092822156656734648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree012.table
  base := (-5353498173145606483215512132435569668517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-7728388219910246491051175615200000000000000)
      constant := (30506438060887016580157960042473554904082508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99044782990123520443/100000000000000000000)
  centralHi := (24761195747530880111/25000000000000000000)
  directionLo := (103448901945368853513/100000000000000000000)
  directionHi := (51724450972684426757/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree013.table
  base := (-2994962083316769668640614278196059219893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-109703966745477475425163405080000000000000)
      constant := (463111741904891233103215143072470934041926) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree013.table
  base := (-6087725902716069454260230902239404729881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 520000000000000000000000000000000000000000
      center := (525)
      previous := (0)
      next := (255)
      square := (33365127106888079477897690560000000000000)
      linear := (-639405995713906760147260400000000000000000)
      constant := (2723723171434329954640454559583550954046188) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103448901945368853513/100000000000000000000)
  centralHi := (51724450972684426757/50000000000000000000)
  directionLo := (26918257732722527187/25000000000000000000)
  directionHi := (107673030930890108749/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree014.table
  base := (-1644365922027027480003859799721403897287/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-117403611462451647612370564440000000000000)
      constant := (533526412280929805537785237130029459697668) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree014.table
  base := (-6661622858833693072455712705644222783799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-8896167668651329272777594784800000000000000)
      constant := (40811750698355238348408641454984505398151876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26918257732722527187/25000000000000000000)
  centralHi := (107673030930890108749/100000000000000000000)
  directionLo := (11173758484049266577/10000000000000000000)
  directionHi := (111737584840492665771/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree015.table
  base := (-3517440007785293552977804461254098890427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (10)
      previous := (0)
      next := (5)
      square := (641637059747847682267263280000000000000)
      linear := (-13900361797713979977730858200000000000000)
      constant := (67805031986784444444626645077491802219146) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree015.table
  base := (-7106930197288970953726452201921858416321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-9480057393021870663640804369600000000000000)
      constant := (46695029448699489710041198194000823710567004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11173758484049266577/10000000000000000000)
  centralHi := (111737584840492665771/100000000000000000000)
  directionLo := (23131877694755499209/20000000000000000000)
  directionHi := (57829694236888748023/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree016.table
  base := (-1477514268970700285352604083564049148617/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18000000000000000000000000000000000000000
      center := (18)
      previous := (0)
      next := (9)
      square := (1154946707546125828081073904000000000000)
      linear := (-26560580179279998397356976632000000000000)
      constant := (138607956988557808341965460911923557662447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree016.table
  base := (-1489796136788809274155450222390546994559/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (1365)
      previous := (0)
      next := (663)
      square := (86749330477909006642533995456000000000000)
      linear := (-2012789423478482410900802790880000000000000)
      constant := (10608222505991246928575026705663990231678116) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23131877694755499209/20000000000000000000)
  centralHi := (57829694236888748023/50000000000000000000)
  directionLo := (59726251385529907999/50000000000000000000)
  directionHi := (119452502771059815999/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree017.table
  base := (-3827928396694809227064041831540035548497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-140502545613374164173992042520000000000000)
      constant := (781727031409222040517134043912279360127054) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree017.table
  base := (-3853996185592635583810105041211923258991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-10647836841762953445367223539200000000000000)
      constant := (59836332538712299300358267420781479753844168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59726251385529907999/50000000000000000000)
  centralHi := (119452502771059815999/100000000000000000000)
  directionLo := (123128821542366478273/100000000000000000000)
  directionHi := (61564410771183239137/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree018.table
  base := (-1963998005187185799001632533434475490199/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (10)
      previous := (0)
      next := (5)
      square := (641637059747847682267263280000000000000)
      linear := (-16466910036705370706799911320000000000000)
      constant := (97351191816025639039106493386262098039204) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree018.table
  base := (-19750252958459004545301096795992307549/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (1365)
      previous := (0)
      next := (663)
      square := (86749330477909006642533995456000000000000)
      linear := (-2246345313226698967246086624800000000000000)
      constant := (13413956318018583421231557155672736007750080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123128821542366478273/100000000000000000000)
  centralHi := (61564410771183239137/50000000000000000000)
  directionLo := (63349256054340941343/50000000000000000000)
  directionHi := (126698512108681882687/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree019.table
  base := (-8000981801762291047926717510649804303719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-155901835047322508548406361240000000000000)
      constant := (976223826774332435654545275124151761266529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree019.table
  base := (-803818507545731184426762532339886788083/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (1365)
      previous := (0)
      next := (663)
      square := (86749330477909006642533995456000000000000)
      linear := (-2363123258100807245418728541760000000000000)
      constant := (14946550837314667031881731861576473062511784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63349256054340941343/50000000000000000000)
  centralHi := (126698512108681882687/100000000000000000000)
  directionLo := (26034069406603100597/20000000000000000000)
  directionHi := (65085173516507751493/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree020.table
  base := (-8101230130451693652272121983686626062719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-163601479764296680735613520600000000000000)
      constant := (1081822696753334208643443262146820365435529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree020.table
  base := (-1626504363954103814768838528386431689873/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (1365)
      previous := (0)
      next := (663)
      square := (86749330477909006642533995456000000000000)
      linear := (-2479901202974915523591370458720000000000000)
      constant := (16563660510807081961705994046810772177645852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26034069406603100597/20000000000000000000)
  centralHi := (65085173516507751493/50000000000000000000)
  directionLo := (267103916278571747/200000000000000000)
  directionHi := (133551958139285873501/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree021.table
  base := (-4082530165358441562177718155280916245769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (10)
      previous := (0)
      next := (5)
      square := (641637059747847682267263280000000000000)
      linear := (-19033458275696761435868964440000000000000)
      constant := (132542491818459631253426462969438167508462) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree021.table
  base := (-1638262799588452402156167771023654308193/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (1365)
      previous := (0)
      next := (663)
      square := (86749330477909006642533995456000000000000)
      linear := (-2596679147849023801764012375680000000000000)
      constant := (18264176349460934204972913317288009687661532) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267103916278571747/200000000000000000)
  centralHi := (133551958139285873501/100000000000000000000)
  directionLo := (8553127123442247507/6250000000000000000)
  directionHi := (136850033975075960113/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree022.table
  base := (-4099565580941027293692836661398058283459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-179000769198245025110027839320000000000000)
      constant := (1309343086778822097457848873374834950897738) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree022.table
  base := (-8221108001517515769419484968928585985587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-13567285463615660399683271463200000000000000)
      constant := (100236066405696715631117309765004275873743188) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8553127123442247507/6250000000000000000)
  centralHi := (136850033975075960113/100000000000000000000)
  directionLo := (140070475386932712809/100000000000000000000)
  directionHi := (14007047538693271281/10000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree023.table
  base := (-8208769713739818572743224552107912647347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-186700413915219197297234998680000000000000)
      constant := (1431156734183256962392051858311028786173877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree023.table
  base := (-4113564218618219336349365961768710479927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-14151175187986201790546481048000000000000000)
      constant := (109560324695055196600981705534188703431138696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140070475386932712809/100000000000000000000)
  centralHi := (14007047538693271281/10000000000000000000)
  directionLo := (71609259791006081199/50000000000000000000)
  directionHi := (143218519582012162399/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree024.table
  base := (-8198237729245778978094237874894755867069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (10)
      previous := (0)
      next := (5)
      square := (641637059747847682267263280000000000000)
      linear := (-21600006514688152164938017560000000000000)
      constant := (173142779210315649000494643405105244132931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree024.table
  base := (-8213545014758698575455393950167720406869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-14735064912356743181409690632800000000000000)
      constant := (119290837891650178464588067473686621004956556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71609259791006081199/50000000000000000000)
  centralHi := (143218519582012162399/100000000000000000000)
  directionLo := (2925976802874901777/2000000000000000000)
  directionHi := (146298840143745088851/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree025.table
  base := (-8170944666853437980300927850213293334101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-202099703349167541671649317400000000000000)
      constant := (1690697237781492213703288739348080359993091) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree025.table
  base := (-1022960693467342803360186233977920506383/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-15318954636727284572272900217600000000000000)
      constant := (129425356393451255084282590859147405901480736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2925976802874901777/2000000000000000000)
  centralHi := (146298840143745088851/100000000000000000000)
  directionLo := (149315628463824769997/100000000000000000000)
  directionHi := (74657814231912384999/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree026.table
  base := (-8129618152985879047054127790675344150791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-209799348066141713858856476760000000000000)
      constant := (1828368860211403329279345204603921902642881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree026.table
  base := (-8140205947650107294716710911766391340373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 520000000000000000000000000000000000000000
      center := (525)
      previous := (0)
      next := (255)
      square := (33365127106888079477897690560000000000000)
      linear := (-1223295720084448151010469984800000000000000)
      constant := (10766314215715562723251788032588147650300604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149315628463824769997/100000000000000000000)
  centralHi := (74657814231912384999/50000000000000000000)
  directionLo := (76136330322141275627/50000000000000000000)
  directionHi := (30454532128856510251/20000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree027.table
  base := (-8076440345609471544491076087667688286969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (10)
      previous := (0)
      next := (5)
      square := (641637059747847682267263280000000000000)
      linear := (-24166554753679542894007070680000000000000)
      constant := (219031137862319651493042893432332311713031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree027.table
  base := (-8085225893517265001304268361614066626413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-16486734085468367353999319387200000000000000)
      constant := (150899590221182816466656017334048890960544812) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76136330322141275627/50000000000000000000)
  centralHi := (30454532128856510251/20000000000000000000)
  directionLo := (155173352918053280269/100000000000000000000)
  directionHi := (15517335291805328027/10000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree028.table
  base := (-8013157026044140034680808619101392609451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-225198637500090058233270795480000000000000)
      constant := (2119415667398033495118789925308087466514941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree028.table
  base := (-2005109276935483366548945031432661966371/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-17070623809838908744862528972000000000000000)
      constant := (162236729039749196963814015887006082042932816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155173352918053280269/100000000000000000000)
  centralHi := (15517335291805328027/10000000000000000000)
  directionLo := (158020807908239074363/100000000000000000000)
  directionHi := (39505201977059768591/25000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree029.table
  base := (-496322804559479864160265848051702546949/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-232898282217064230420477954840000000000000)
      constant := (2272762570014917084543088504200554833239344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree029.table
  base := (-7947189769077598814885333351632459037853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-17654513534209450135725738556800000000000000)
      constant := (173972588539164100272913237170796457690411372) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158020807908239074363/100000000000000000000)
  centralHi := (39505201977059768591/25000000000000000000)
  directionLo := (20102231688964004449/12500000000000000000)
  directionHi := (160817853511712035593/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree030.table
  base := (-7861581281807397127735073091029314296931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (10)
      previous := (0)
      next := (5)
      square := (641637059747847682267263280000000000000)
      linear := (-26733102992670933623076123800000000000000)
      constant := (270145654672472202426882090908970685703069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree030.table
  base := (-7866561477109268131642470705087436703121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-18238403258579991526588948141600000000000000)
      constant := (186106440262108061604987470343360892788690204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20102231688964004449/12500000000000000000)
  centralHi := (160817853511712035593/100000000000000000000)
  directionLo := (32713415159078912293/20000000000000000000)
  directionHi := (81783537897697280733/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree031.table
  base := (-3887650110299337910084308826358167594803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-248297571651012574794892273560000000000000)
      constant := (2595052587798145306077562713045552983293546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree031.table
  base := (-7779412291333385505023327132314349128779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-18822292982950532917452157726400000000000000)
      constant := (198637702808361484756172768181055499988945396) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32713415159078912293/20000000000000000000)
  centralHi := (81783537897697280733/50000000000000000000)
  directionLo := (166270846994890321109/100000000000000000000)
  directionHi := (16627084699489032111/10000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree032.table
  base := (-3841518457205037713597060918076504464541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-255997216367986746982099432920000000000000)
      constant := (2763981220226842483539997077554622919638262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree032.table
  base := (-480401791037687715980522947653631921601/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-19406182707321074308315367311200000000000000)
      constant := (211565912141203706222502656662178317135963584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (166270846994890321109/100000000000000000000)
  centralHi := (16627084699489032111/10000000000000000000)
  directionLo := (21116418684780313781/12500000000000000000)
  directionHi := (168931349478242510249/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree033.table
  base := (-474085224566552691477217630560290791849/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (10)
      previous := (0)
      next := (5)
      square := (641637059747847682267263280000000000000)
      linear := (-29299651231662324352145176920000000000000)
      constant := (326454626585548014466202982631035347330416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree033.table
  base := (-3794079229492421124420581735764056124921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-19990072431691615699178576896000000000000000)
      constant := (224890697889653623104699520657746996119106808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21116418684780313781/12500000000000000000)
  centralHi := (168931349478242510249/100000000000000000000)
  directionLo := (171550596363527644699/100000000000000000000)
  directionHi := (1715505963635276447/1000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree034.table
  base := (-7482738089185626521149111442414716113631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-271396505801935091356513751640000000000000)
      constant := (3117379724433810415920144294138267554977321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree034.table
  base := (-3742519501488454815810932433300570660763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-20573962156062157090041786480800000000000000)
      constant := (238611764435870582165696619574177628466648424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171550596363527644699/100000000000000000000)
  centralHi := (1715505963635276447/1000000000000000000)
  directionLo := (17413044934423118483/10000000000000000000)
  directionHi := (174130449344231184831/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree035.table
  base := (-7375526716581606629355002705630027538569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-279096150518909263543720911000000000000000)
      constant := (3301842178894194713246369493649329752152879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree035.table
  base := (-1844354834854592299316910232411281291909/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-21157851880432698480904996065600000000000000)
      constant := (252728875821487308816465626774059895386678064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17413044934423118483/10000000000000000000)
  centralHi := (174130449344231184831/100000000000000000000)
  directionLo := (176672634171129460127/100000000000000000000)
  directionHi := (5521019817847795629/3125000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree036.table
  base := (-7264022572898083470017804238750631222723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (10)
      previous := (0)
      next := (5)
      square := (641637059747847682267263280000000000000)
      linear := (-31866199470653715081214230040000000000000)
      constant := (387941818308030813493180067441249368777277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree036.table
  base := (-363278904240927606314202541488171268899/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (1365)
      previous := (0)
      next := (663)
      square := (86749330477909006642533995456000000000000)
      linear := (-4348348320960647974353641130080000000000000)
      constant := (53448368740348699035796956851815984888897104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176672634171129460127/100000000000000000000)
  centralHi := (5521019817847795629/3125000000000000000)
  directionLo := (179178754156589723997/100000000000000000000)
  directionHi := (89589377078294861999/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree037.table
  base := (-7148460181683214559071131329310658608999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-294495439952857607918135229720000000000000)
      constant := (3686280171356124822853495096516204072519009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree037.table
  base := (-7149737642498799714475467919231080782399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-22325631329173781262631415235200000000000000)
      constant := (282150517731993914537290335643099789391098276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179178754156589723997/100000000000000000000)
  centralHi := (89589377078294861999/50000000000000000000)
  directionLo := (90825151000768363171/50000000000000000000)
  directionHi := (181650302001536726343/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree038.table
  base := (-1405805441199730886570297773954169440369/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18000000000000000000000000000000000000000
      center := (18)
      previous := (0)
      next := (9)
      square := (1154946707546125828081073904000000000000)
      linear := (-60439016933966356021068477816000000000000)
      constant := (777250381935636465332792883650412475036679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree038.table
  base := (-878759444014292301765236550550111469113/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-22909521053544322653494624820000000000000000)
      constant := (297454777895431633809641000786624997175036896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90825151000768363171/50000000000000000000)
  centralHi := (181650302001536726343/100000000000000000000)
  directionLo := (23011083774112862257/12500000000000000000)
  directionHi := (184088670192902898057/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree039.table
  base := (-6905873819276639646543258677306118281177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (10)
      previous := (0)
      next := (5)
      square := (641637059747847682267263280000000000000)
      linear := (-34432747709645105810283283160000000000000)
      constant := (454598914241951078208152126202693881718823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree039.table
  base := (-6906733547413868717392230964659939166487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 520000000000000000000000000000000000000000
      center := (525)
      previous := (0)
      next := (255)
      square := (33365127106888079477897690560000000000000)
      linear := (-1807185444454989541873679569600000000000000)
      constant := (24088809875387887035640815290337683163342676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23011083774112862257/12500000000000000000)
  centralHi := (184088670192902898057/100000000000000000000)
  directionLo := (46623790044309229127/25000000000000000000)
  directionHi := (186495160177236916509/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree040.table
  base := (-6779120201985548330553879379273108607803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-317594374103780124479756707800000000000000)
      constant := (4301694045230041551308042301586542022529773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree040.table
  base := (-3389912392503957123059364687034487346921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-24077300502285405435221043989600000000000000)
      constant := (329249692691957893530000531463129373106962808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46623790044309229127/25000000000000000000)
  centralHi := (186495160177236916509/100000000000000000000)
  directionLo := (94435495241030970819/50000000000000000000)
  directionHi := (188870990482061941639/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree041.table
  base := (-6648862538952868348576367430256757230739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-325294018820754296666963867160000000000000)
      constant := (4517162495172180478194746767447689184923349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree041.table
  base := (-6649439613472149164562005019245019122231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-24661190226655946826084253574400000000000000)
      constant := (345740209755540564274610621499490367073371844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94435495241030970819/50000000000000000000)
  centralHi := (188870990482061941639/100000000000000000000)
  directionLo := (191217303928846907229/100000000000000000000)
  directionHi := (19121730392884690723/10000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree042.table
  base := (-814397227152957459246754631117746877081/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (10)
      previous := (0)
      next := (5)
      square := (641637059747847682267263280000000000000)
      linear := (-36999295948636496539352336280000000000000)
      constant := (526421653902285660530356967271058024983352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree042.table
  base := (-6515650177535384431890449814667009807543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-25245079951026488216947463159200000000000000)
      constant := (362626030800953867488763035949285101370100932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191217303928846907229/100000000000000000000)
  centralHi := (19121730392884690723/10000000000000000000)
  directionLo := (1548281392470170103/800000000000000000)
  directionHi := (48383793514692815719/25000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree043.table
  base := (-797265958044468650634344873845155092637/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-340693308254702641041378185880000000000000)
      constant := (4963590660427192508958489278763148833330136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree043.table
  base := (-6378514092583906979923426930710088747361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-25828969675397029607810672744000000000000000)
      constant := (379907116880196673206547885309339980006783964) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1548281392470170103/800000000000000000)
  centralHi := (48383793514692815719/25000000000000000000)
  directionLo := (97912805436904890437/50000000000000000000)
  directionHi := (1566604886990478247/800000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree044.table
  base := (-6237761419071380027048382766856361682311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-348392952971676813228585345240000000000000)
      constant := (5194549377043544982984047841818292744859201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree044.table
  base := (-97469959018967070472841137579389700043/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-26412859399767570998673882328800000000000000)
      constant := (397583436884697966653682963587765284017339648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97912805436904890437/50000000000000000000)
  centralHi := (1566604886990478247/800000000000000000)
  directionLo := (99044782990123520443/50000000000000000000)
  directionHi := (198089565980247040887/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree045.table
  base := (-380882411737491640817529711876826486139/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (10)
      previous := (0)
      next := (5)
      square := (641637059747847682267263280000000000000)
      linear := (-39565844187627887268421389400000000000000)
      constant := (603407853267973837759024254609970776221776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree045.table
  base := (-6094376793655019122889358516378469376313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-26996749124138112389537091913600000000000000)
      constant := (415654965963190485434579295615428154701612412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99044782990123520443/50000000000000000000)
  centralHi := (198089565980247040887/100000000000000000000)
  directionLo := (801311748835715241/400000000000000000)
  directionHi := (200327937208928810251/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree046.table
  base := (-2973615404968878290553555591566109833177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-363792242405625157602999663960000000000000)
      constant := (5671954282777282241218575958871810023002814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree046.table
  base := (-2973720857817260877461552192821554856279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-27580638848508653780400301498400000000000000)
      constant := (434121684259034618731745721575305257834310792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (801311748835715241/400000000000000000)
  centralHi := (200327937208928810251/100000000000000000000)
  directionLo := (40508314555175658373/20000000000000000000)
  directionHi := (101270786387939145933/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree047.table
  base := (-231884937203467362217397727761944613907/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18000000000000000000000000000000000000000
      center := (18)
      previous := (0)
      next := (9)
      square := (1154946707546125828081073904000000000000)
      linear := (-74298377424519865958041364664000000000000)
      constant := (1183679991807736677949472193306712492374185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree047.table
  base := (-1159459123821221852111812159324569257931/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (1365)
      previous := (0)
      next := (663)
      square := (86749330477909006642533995456000000000000)
      linear := (-5632905714575839034252702216640000000000000)
      constant := (90596715180497131871949150393596591181638644) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40508314555175658373/20000000000000000000)
  centralHi := (101270786387939145933/50000000000000000000)
  directionLo := (204731275037958674717/100000000000000000000)
  directionHi := (102365637518979337359/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree048.table
  base := (-1128763351175228202674695740140405480407/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (2)
      previous := (0)
      next := (1)
      square := (128327411949569536453452656000000000000)
      linear := (-8426478485323855599498088504000000000000)
      constant := (137111278342828945652928616643859594519593) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree048.table
  base := (-1128791454399772936425169580334855640963/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (1365)
      previous := (0)
      next := (663)
      square := (86749330477909006642533995456000000000000)
      linear := (-5749683659449947312425344133600000000000000)
      constant := (94448125641284709436393047914093637586709012) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204731275037958674717/100000000000000000000)
  centralHi := (102365637518979337359/50000000000000000000)
  directionLo := (103448901945368853513/50000000000000000000)
  directionHi := (206897803890737707027/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree049.table
  base := (-5487327064256189233380655053672430534891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-386891176556547674164621142040000000000000)
      constant := (6426776835450589179115734870036948125185981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree049.table
  base := (-5487441683762985773057600749736460812531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-29332308021620277952989930252800000000000000)
      constant := (491892831024459948517082709089678152490729044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103448901945368853513/50000000000000000000)
  centralHi := (206897803890737707027/100000000000000000000)
  directionLo := (52260469962338669499/25000000000000000000)
  directionHi := (209041879849354677997/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree050.table
  base := (-1331916851641862016641549841077490072629/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-394590821273521846351828301400000000000000)
      constant := (6688707771646477689789214785721210357385356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree050.table
  base := (-1331940215804075317817393734686346752531/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-29916197745990819343853139837600000000000000)
      constant := (511940176238634011138267447741408118381156176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52260469962338669499/25000000000000000000)
  centralHi := (209041879849354677997/100000000000000000000)
  directionLo := (211164186847803137811/100000000000000000000)
  directionHi := (52791046711950784453/25000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree051.table
  base := (-258242412631683816550347227725651643321/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (2)
      previous := (0)
      next := (1)
      square := (128327411949569536453452656000000000000)
      linear := (-8939788133122133745311899128000000000000)
      constant := (154573338661923427934211911105097393426716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree051.table
  base := (-51649244234008697193449428838641512353/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (1365)
      previous := (0)
      next := (663)
      square := (86749330477909006642533995456000000000000)
      linear := (-6100017494072272146943269884480000000000000)
      constant := (106476531470105860694146646194601566752987440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211164186847803137811/100000000000000000000)
  centralHi := (52791046711950784453/25000000000000000000)
  directionLo := (213265374787460034137/100000000000000000000)
  directionHi := (106632687393730017069/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree052.table
  base := (-999775601214547641898737385712767713077/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18000000000000000000000000000000000000000
      center := (18)
      previous := (0)
      next := (9)
      square := (1154946707546125828081073904000000000000)
      linear := (-81998022141494038145248524024000000000000)
      constant := (1445610832847651620644316269064585090582307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree052.table
  base := (-4998940064342196751315525238137334130057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 520000000000000000000000000000000000000000
      center := (525)
      previous := (0)
      next := (255)
      square := (33365127106888079477897690560000000000000)
      linear := (-2391075168825530932736889154400000000000000)
      constant := (42555405319609891054298042155616858625237036) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213265374787460034137/100000000000000000000)
  centralHi := (106632687393730017069/50000000000000000000)
  directionLo := (215346061861780217497/100000000000000000000)
  directionHi := (107673030930890108749/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree053.table
  base := (-120744085414555195615950864686963487613/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18000000000000000000000000000000000000000
      center := (18)
      previous := (0)
      next := (9)
      square := (1154946707546125828081073904000000000000)
      linear := (-83537951084888872582689955896000000000000)
      constant := (1501093896850862212246369269918538628891864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree053.table
  base := (-965962791673061504668273144384555406971/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (1365)
      previous := (0)
      next := (663)
      square := (86749330477909006642533995456000000000000)
      linear := (-6333573383820488703288553718400000000000000)
      constant := (114890601495868026967625441867296040544887604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215346061861780217497/100000000000000000000)
  centralHi := (107673030930890108749/50000000000000000000)
  directionLo := (217406836680725269753/100000000000000000000)
  directionHi := (108703418340362634877/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree054.table
  base := (-2328754954902156297521835189119095791507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (10)
      previous := (0)
      next := (5)
      square := (641637059747847682267263280000000000000)
      linear := (-47265488904602059455628548760000000000000)
      constant := (865338461222659231589210874101761808416986) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree054.table
  base := (-4657551057643342621462166251208885545009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-32251756643472984907305978176800000000000000)
      constant := (596080868976094913831328376418182793371573916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217406836680725269753/100000000000000000000)
  centralHi := (108703418340362634877/50000000000000000000)
  directionLo := (8777930408624705331/4000000000000000000)
  directionHi := (54862065053904408319/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree055.table
  base := (-4482121851253735356767321109491473089769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-433089044858392707287864098200000000000000)
      constant := (8075784125197492026910225356014576742192079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree055.table
  base := (-560269417460141162861363247773732170439/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-32835646367843526298169187761600000000000000)
      constant := (618103850956399657459602075358539656422265888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8777930408624705331/4000000000000000000)
  centralHi := (54862065053904408319/25000000000000000000)
  directionLo := (221470867582631073359/100000000000000000000)
  directionHi := (2768385844782888417/1250000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree056.table
  base := (-2151801378747452596669678026350589063331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-440788689575366879475071257560000000000000)
      constant := (8368683375185908027302055493445689396860042) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree056.table
  base := (-4303630003265302117296583743828268388389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-33419536092214067689032397346400000000000000)
      constant := (640521951257874600767372062949172090569449036) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221470867582631073359/100000000000000000000)
  centralHi := (2768385844782888417/1250000000000000000)
  directionLo := (223475169680985331541/100000000000000000000)
  directionHi := (111737584840492665771/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree057.table
  base := (-2060977732558970212520752904001812618561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (10)
      previous := (0)
      next := (5)
      square := (641637059747847682267263280000000000000)
      linear := (-49832037143593450184697601880000000000000)
      constant := (962971541715541113399539189311996374762878) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree057.table
  base := (-4121977624881988605225017411062756830609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-34003425816584609079895606931200000000000000)
      constant := (663335168138815121537229366306621576382508316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223475169680985331541/100000000000000000000)
  centralHi := (111737584840492665771/50000000000000000000)
  directionLo := (112730827350027756153/50000000000000000000)
  directionHi := (225461654700055512307/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree058.table
  base := (-78743645319049440570734233630011968289/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18000000000000000000000000000000000000000
      center := (18)
      previous := (0)
      next := (9)
      square := (1154946707546125828081073904000000000000)
      linear := (-91237595801863044769897115256000000000000)
      constant := (1793993121066582265600330103069298922853990) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree058.table
  base := (-1968600141791767032517104445257938041161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-34587315540955150470758816516000000000000000)
      constant := (686543500193781834347483976142011267768350328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112730827350027756153/50000000000000000000)
  centralHi := (225461654700055512307/100000000000000000000)
  directionLo := (113715394753996415739/50000000000000000000)
  directionHi := (227430789507992831479/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree059.table
  base := (-1874642507635329530517324961639097103417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-463887623726289396036692735640000000000000)
      constant := (9278348548167582518004561841810496252138494) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree059.table
  base := (-937324915168505417426207831048425500249/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-35171205265325691861622026100800000000000000)
      constant := (710146946286213178973200957411345057447326704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113715394753996415739/50000000000000000000)
  centralHi := (227430789507992831479/100000000000000000000)
  directionLo := (45876604186609462043/20000000000000000000)
  directionHi := (28672877616630913777/12500000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree060.table
  base := (-177913260919020004052866278751022912131/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (2)
      previous := (0)
      next := (1)
      square := (128327411949569536453452656000000000000)
      linear := (-10479717076516968182753331000000000000000)
      constant := (213153170897691388968397525284995908351476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree060.table
  base := (-111196159978034241216199577510718333977/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-35755094989696233252485235685600000000000000)
      constant := (734145505494624051867795614919288140999409536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45876604186609462043/20000000000000000000)
  centralHi := (28672877616630913777/12500000000000000000)
  directionLo := (231318776947554992091/100000000000000000000)
  directionHi := (57829694236888748023/25000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree061.table
  base := (-1682062049964759707343587843894187364087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-479286913160237740411107054360000000000000)
      constant := (9910598020996670865786888969929904627446434) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree061.table
  base := (-3364133767983091893502639893978898862477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-36338984714066774643348445270400000000000000)
      constant := (758539177069647946111028379164170264368965548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231318776947554992091/100000000000000000000)
  centralHi := (57829694236888748023/25000000000000000000)
  directionLo := (116619233881738582979/50000000000000000000)
  directionHi := (233238467763477165959/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree062.table
  base := (-98964458105548243901043458629052420723/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-486986557877211912598314213720000000000000)
      constant := (10234464530974121863945380124394832902831776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree062.table
  base := (-316687051139326645507527247377822767849/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (1365)
      previous := (0)
      next := (663)
      square := (86749330477909006642533995456000000000000)
      linear := (-7384574887687463206842330971040000000000000)
      constant := (156665592079946770494009139570345183617868152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116619233881738582979/50000000000000000000)
  centralHi := (233238467763477165959/100000000000000000000)
  directionLo := (235142486847435666589/100000000000000000000)
  directionHi := (23514248684743566659/10000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree063.table
  base := (-741620428850091916008997593629838645003/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (10)
      previous := (0)
      next := (5)
      square := (641637059747847682267263280000000000000)
      linear := (-54965133621576231642835708120000000000000)
      constant := (1173721356995598049815611324745480645419988) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree063.table
  base := (-2966488090845135855159585869501453073033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-37506764162807857425074864440000000000000000)
      constant := (808511854983751129823617819066717017722629692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235142486847435666589/100000000000000000000)
  centralHi := (23514248684743566659/10000000000000000000)
  directionLo := (47406242372471722309/20000000000000000000)
  directionHi := (118515605931179305773/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree064.table
  base := (-1381490970720030862449172529512093700559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-502385847311160256972728532440000000000000)
      constant := (10897681060894473982378824032388782313389938) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree064.table
  base := (-2762987116681181815174120250391120432277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-38090653887178398815938074024800000000000000)
      constant := (834090860409108260528065809654735602587780748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47406242372471722309/20000000000000000000)
  centralHi := (118515605931179305773/50000000000000000000)
  directionLo := (59726251385529907999/25000000000000000000)
  directionHi := (238905005542119631997/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree065.table
  base := (-319545486771206644151437129798466436773/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-510085492028134429159935691800000000000000)
      constant := (11237031069766339221568227072654510416552344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree065.table
  base := (-51127361882535669047542843832826347161/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104000000000000000000000000000000000000000
      center := (105)
      previous := (0)
      next := (51)
      square := (6673025421377615895579538112000000000000)
      linear := (-594992978639214464720019747840000000000000)
      constant := (13231768866681121358463432021706930299476280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59726251385529907999/25000000000000000000)
  centralHi := (238905005542119631997/100000000000000000000)
  directionLo := (6019105412622693593/2500000000000000000)
  directionHi := (240764216504907743721/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree066.table
  base := (-2346628036288769823040340167778486673131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (10)
      previous := (0)
      next := (5)
      square := (641637059747847682267263280000000000000)
      linear := (-57531681860567622371904761240000000000000)
      constant := (1286838026156853501671347444312221513326869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree066.table
  base := (-18773051551607441794093394554841863947/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (1365)
      previous := (0)
      next := (663)
      square := (86749330477909006642533995456000000000000)
      linear := (-7851686667183896319532898638880000000000000)
      constant := (177286840494961035253304870208023172499295700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6019105412622693593/2500000000000000000)
  centralHi := (240764216504907743721/100000000000000000000)
  directionLo := (242609180010493355417/100000000000000000000)
  directionHi := (121304590005246677709/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree067.table
  base := (-1066887377391448770644856103462698323569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-525484781462082773534350010520000000000000)
      constant := (11931214554347631490538380271017671430175758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree067.table
  base := (-2133777518978066837620355455156330657369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-39842323060290022988527702779200000000000000)
      constant := (913198538592195799805477794698814320475618556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242609180010493355417/100000000000000000000)
  centralHi := (121304590005246677709/50000000000000000000)
  directionLo := (48888043733209798797/20000000000000000000)
  directionHi := (122220109333024496993/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree068.table
  base := (-59931386736015216483713417411912672999/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-533184426179056945721557169880000000000000)
      constant := (12286048023641085092481313943465369150176288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree068.table
  base := (-958903308643886186859877756433320445081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-40426212784660564379390912364000000000000000)
      constant := (940357984484942963458047211125302150758250488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48888043733209798797/20000000000000000000)
  centralHi := (122220109333024496993/50000000000000000000)
  directionLo := (123128821542366478273/50000000000000000000)
  directionHi := (246257643084732956547/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree069.table
  base := (-169871717513693895858917032844855080689/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (2)
      previous := (0)
      next := (1)
      square := (128327411949569536453452656000000000000)
      linear := (-12019646019911802620194762872000000000000)
      constant := (281023169795626393601735437950310289838622) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree069.table
  base := (-424679748192516470149425311420756301693/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-41010102509031105770254121948800000000000000)
      constant := (967912539981417014347759029434418274960222128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123128821542366478273/50000000000000000000)
  centralHi := (246257643084732956547/100000000000000000000)
  directionLo := (15503859531302702023/6250000000000000000)
  directionHi := (248061752500843232369/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree070.table
  base := (-73825669505676656868531341708981329021/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18000000000000000000000000000000000000000
      center := (18)
      previous := (0)
      next := (9)
      square := (1154946707546125828081073904000000000000)
      linear := (-109716743122601058019194297720000000000000)
      constant := (2602239680740948766760794707698476672155244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree070.table
  base := (-1476514863569328722057360889053249058707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-41593992233401647161117331533600000000000000)
      constant := (995862204934152350672682307899000003636314068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15503859531302702023/6250000000000000000)
  centralHi := (248061752500843232369/100000000000000000000)
  directionLo := (124926417672495798219/50000000000000000000)
  directionHi := (249852835344991596439/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree071.table
  base := (-312798306158847655060443667202480599051/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-556283360329979462283178647960000000000000)
      constant := (13381515310508375367251183253500710698434164) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree071.table
  base := (-1251194418842252144795320313190950816773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-42177881957772188551980541118400000000000000)
      constant := (1024206979215279049150050154470782917247861452) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124926417672495798219/50000000000000000000)
  centralHi := (249852835344991596439/100000000000000000000)
  directionLo := (251631169782428504839/100000000000000000000)
  directionHi := (6290779244560712621/2500000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree072.table
  base := (-127844607059973402894605668767668280393/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (10)
      previous := (0)
      next := (5)
      square := (641637059747847682267263280000000000000)
      linear := (-62664778338550403830042867480000000000000)
      constant := (1528554817734898536675126196569858653756856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree072.table
  base := (-1022757824169359901595308281415561540647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-42761771682142729942843750703200000000000000)
      constant := (1052946862712864675722980768505763080398522628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251631169782428504839/100000000000000000000)
  centralHi := (6290779244560712621/2500000000000000000)
  directionLo := (253397024217363765373/100000000000000000000)
  directionHi := (126698512108681882687/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree073.table
  base := (-791204441903908752505781890949070304059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-571682649763927806657592966680000000000000)
      constant := (14137632549615563550021321598261458367263469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree073.table
  base := (-791205225891133501795369471630553912897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-43345661406513271333706960288000000000000000)
      constant := (1082081855327983064891161631801677745554881628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253397024217363765373/100000000000000000000)
  centralHi := (126698512108681882687/50000000000000000000)
  directionLo := (127575328882935979777/50000000000000000000)
  directionHi := (51030131553174391911/20000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree074.table
  base := (-55653611954576227648771757394848123407/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18000000000000000000000000000000000000000
      center := (18)
      previous := (0)
      next := (9)
      square := (1154946707546125828081073904000000000000)
      linear := (-115876458896180395768960025208000000000000)
      constant := (2904686575853012692694589708270892733778674) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree074.table
  base := (-556536754585080809984020624647083926711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-43929551130883812724570169872800000000000000)
      constant := (1111611956972363821338130907041738571265543364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127575328882935979777/50000000000000000000)
  centralHi := (51030131553174391911/20000000000000000000)
  directionLo := (64223080174935452881/25000000000000000000)
  directionHi := (10275692827989672461/4000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree075.table
  base := (-31875201356045279654338113897011847621/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (2)
      previous := (0)
      next := (1)
      square := (128327411949569536453452656000000000000)
      linear := (-13046265315508358911822384120000000000000)
      constant := (331430985498782013898178889772205976304758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree075.table
  base := (-318752527856443343795851828093745936693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-44513440855254354115433379457600000000000000)
      constant := (1141537167566505801797967611326708627746795532) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64223080174935452881/25000000000000000000)
  centralHi := (10275692827989672461/4000000000000000000)
  directionLo := (258622254863422133783/100000000000000000000)
  directionHi := (32327781857927766723/12500000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree076.table
  base := (-9731529518003774145944448858659437971/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-594781583914850323219214444760000000000000)
      constant := (15310516953146180586932173046402176520466088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree076.table
  base := (-77852652580404023256075840541964591661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-45097330579624895506296589042400000000000000)
      constant := (1171857487038161382616734700831793631936037164) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258622254863422133783/100000000000000000000)
  centralHi := (32327781857927766723/12500000000000000000)
  directionLo := (26034069406603100597/10000000000000000000)
  directionHi := (260340694066031005971/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree077.table
  base := (83081555216646862561385729830928201461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-602481228631824495406421604120000000000000)
      constant := (15711800695447601441738664672816956707626298) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree077.table
  base := (20770346661768015852908918349808897683/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-45681220303995436897159798627200000000000000)
      constant := (1202572915321117112109659239226935766518669664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26034069406603100597/10000000000000000000)
  centralHi := (260340694066031005971/100000000000000000000)
  directionLo := (65511966112556791321/25000000000000000000)
  directionHi := (52409572890045433057/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree078.table
  base := (807214711302897907867961275506720019/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (10)
      previous := (0)
      next := (5)
      square := (641637059747847682267263280000000000000)
      linear := (-67797874816533185288180973720000000000000)
      constant := (1790916174833732585863559120493059440649728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree078.table
  base := (41329365929139679691013488287070922309/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104000000000000000000000000000000000000000
      center := (105)
      previous := (0)
      next := (51)
      square := (6673025421377615895579538112000000000000)
      linear := (-711770923513322742892661664800000000000000)
      constant := (18979745420834020716361500883581855375920136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65511966112556791321/25000000000000000000)
  centralHi := (52409572890045433057/20000000000000000000)
  directionLo := (263743984839591191901/100000000000000000000)
  directionHi := (131871992419795595951/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree079.table
  base := (663540142093762771887201589978885130999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-617880518065772839780835922840000000000000)
      constant := (16529851586530943886617716228629809966178991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree079.table
  base := (663539921235843206909045638678516050207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-46848999752736519678886217796800000000000000)
      constant := (1265189098080541440690905118318246676849939932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263743984839591191901/100000000000000000000)
  centralHi := (131871992419795595951/50000000000000000000)
  directionLo := (265429267066027190929/100000000000000000000)
  directionHi := (26542926706602719093/10000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree080.table
  base := (91690165901839524626887664720605425111/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18000000000000000000000000000000000000000
      center := (18)
      previous := (0)
      next := (9)
      square := (1154946707546125828081073904000000000000)
      linear := (-125116032556549402393608616440000000000000)
      constant := (3389323746759887772560688861164970897651998) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree080.table
  base := (91690148030385082876890578722923141939/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (1365)
      previous := (0)
      next := (663)
      square := (86749330477909006642533995456000000000000)
      linear := (-9486577895421412213949885476320000000000000)
      constant := (259417970489364523780583875950433392087901528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (265429267066027190929/100000000000000000000)
  centralHi := (26542926706602719093/10000000000000000000)
  directionLo := (267103916278571747/100000000000000000)
  directionHi := (267103916278571747001/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree081.table
  base := (1173378406845188747430839384392873269657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (10)
      previous := (0)
      next := (5)
      square := (641637059747847682267263280000000000000)
      linear := (-70364423055524576017250026840000000000000)
      constant := (1929838557180448452187592564264392873269657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree081.table
  base := (117337826225488660248905475206784011901/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (1365)
      previous := (0)
      next := (663)
      square := (86749330477909006642533995456000000000000)
      linear := (-9603355840295520492122527393280000000000000)
      constant := (265877143080573656170195979036979571984090152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267103916278571747/100000000000000000)
  centralHi := (267103916278571747001/100000000000000000000)
  directionLo := (67192032808721146499/25000000000000000000)
  directionHi := (268768131234884585997/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree082.table
  base := (358242578442674833429807234000376830627/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-640979452216695356342457400920000000000000)
      constant := (17795636428358504511797497798504013565902572) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree082.table
  base := (716485098403318574709006098818256191969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-48600668925848143851475846551200000000000000)
      constant := (1362076686901167582691118263909602282371542088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67192032808721146499/25000000000000000000)
  centralHi := (268768131234884585997/100000000000000000000)
  directionLo := (135211052288296704283/50000000000000000000)
  directionHi := (270422104576593408567/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree083.table
  base := (423919327931925300558744023947644221071/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-648679096933669528529664560280000000000000)
      constant := (18227886974390239156904846843342115191958556) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree083.table
  base := (1695677217125479350247209534926346522867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-49184558650218685242339056136000000000000000)
      constant := (1395162766896540995194681893560110210249458092) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135211052288296704283/50000000000000000000)
  centralHi := (270422104576593408567/100000000000000000000)
  directionLo := (26568947567341083/9765625000000000)
  directionHi := (272066023089572689921/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree084.table
  base := (1961499335914063853462872332087701228823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (10)
      previous := (0)
      next := (5)
      square := (641637059747847682267263280000000000000)
      linear := (-72930971294515966746319079960000000000000)
      constant := (2073922072459557870057193704012087701228823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree084.table
  base := (392299851881898265379562906824849049329/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (1365)
      previous := (0)
      next := (663)
      square := (86749330477909006642533995456000000000000)
      linear := (-9953689674917845326640453144160000000000000)
      constant := (285728791069171683834417898709813597957346404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26568947567341083/9765625000000000)
  centralHi := (272066023089572689921/100000000000000000000)
  directionLo := (8553127123442247507/3125000000000000000)
  directionHi := (10948002718006076809/4000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree085.table
  base := (223043632440608688560057471271561456479/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18000000000000000000000000000000000000000
      center := (18)
      previous := (0)
      next := (9)
      square := (1154946707546125828081073904000000000000)
      linear := (-132815677273523574580815775800000000000000)
      constant := (3821574292207707245802193238082888106216622) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree085.table
  base := (2230436262545775126532065997521946408637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-50352338098959768024065475305600000000000000)
      constant := (1462520252207807535607222737306824835772238612) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8553127123442247507/3125000000000000000)
  centralHi := (10948002718006076809/4000000000000000000)
  directionLo := (137662207479085973601/50000000000000000000)
  directionHi := (275324414958171947203/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree086.table
  base := (1251244108919914754864321118818401375307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-671778031084592045091286038360000000000000)
      constant := (19555605400563509885293240437258731224755526) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree086.table
  base := (1251244083913759953935156163624102479461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-50936227823330309414928684890400000000000000)
      constant := (1496791657442702540371376580353219786552231272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137662207479085973601/50000000000000000000)
  centralHi := (275324414958171947203/100000000000000000000)
  directionLo := (55387846951547605713/20000000000000000000)
  directionHi := (138469617378869014283/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree087.table
  base := (2777654959147242676382032273497546335067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (10)
      previous := (0)
      next := (5)
      square := (641637059747847682267263280000000000000)
      linear := (-75497519533507357475388133080000000000000)
      constant := (2223166718910814373101820076993497546335067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree087.table
  base := (555530983743830929455819046203883521993/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (1365)
      previous := (0)
      next := (663)
      square := (86749330477909006642533995456000000000000)
      linear := (-10304023509540170161158378895040000000000000)
      constant := (306291634202465077490514960976533825260867268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55387846951547605713/20000000000000000000)
  centralHi := (138469617378869014283/50000000000000000000)
  directionLo := (34818086630806780057/12500000000000000000)
  directionHi := (278544693046454240457/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree088.table
  base := (1527968246668264762819607092908327860037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-687177320518540389465700357080000000000000)
      constant := (20466556669445068475141093181752349901480666) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree088.table
  base := (611187292132054226524929317143980950277/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (1365)
      previous := (0)
      next := (663)
      square := (86749330477909006642533995456000000000000)
      linear := (-10420801454414278439331020812000000000000000)
      constant := (313303958575958648179882996728789331122387252) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34818086630806780057/12500000000000000000)
  centralHi := (278544693046454240457/100000000000000000000)
  directionLo := (280140950773865425619/100000000000000000000)
  directionHi := (14007047538693271281/5000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree089.table
  base := (1668666383654127627327662523612982803357/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-694876965235514561652907516440000000000000)
      constant := (20929773997828832323741774137345033690460426) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree089.table
  base := (41716659261260750804996116513938480703/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (1365)
      previous := (0)
      next := (663)
      square := (86749330477909006642533995456000000000000)
      linear := (-10537579399288386717503662728960000000000000)
      constant := (320395304601889418885086039467514758607283648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280140950773865425619/100000000000000000000)
  centralHi := (14007047538693271281/5000000000000000000)
  directionLo := (140864082164889685837/50000000000000000000)
  directionHi := (11269126573191174867/4000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree090.table
  base := (3621843729700404869616613189184915745627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (10)
      previous := (0)
      next := (5)
      square := (641637059747847682267263280000000000000)
      linear := (-78064067772498748204457186200000000000000)
      constant := (2377572494987373640974899977189184915745627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree090.table
  base := (1810921854180945111133694243471279122391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-53271786720812474978381523229600000000000000)
      constant := (1637828361366757522925672745537173169373472632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140864082164889685837/50000000000000000000)
  centralHi := (11269126573191174867/4000000000000000000)
  directionLo := (283306485723092912457/100000000000000000000)
  directionHi := (141653242861546456229/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree091.table
  base := (3909469330756930199332586426375784805707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-710276254669462906027321835160000000000000)
      constant := (21871692040169855376697355724157382063251363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree091.table
  base := (3909469313516448528597327452347737595621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 520000000000000000000000000000000000000000
      center := (525)
      previous := (0)
      next := (255)
      square := (33365127106888079477897690560000000000000)
      linear := (-4142744341937155105326517908800000000000000)
      constant := (128775023686018794858435728200022082354972292) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (283306485723092912457/100000000000000000000)
  centralHi := (141653242861546456229/50000000000000000000)
  directionLo := (71219015687925180067/25000000000000000000)
  directionHi := (284876062751700720269/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree092.table
  base := (4200209522215402833332914739256922722491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-717975899386437078214528994520000000000000)
      constant := (22350392753244948291817308955533312304502419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree092.table
  base := (210010475414380391141544044051995699461/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (1365)
      previous := (0)
      next := (663)
      square := (86749330477909006642533995456000000000000)
      linear := (-10887913233910711552021588479840000000000000)
      constant := (342143472526281504473373545959916596371342544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71219015687925180067/25000000000000000000)
  centralHi := (284876062751700720269/100000000000000000000)
  directionLo := (71609259791006081199/25000000000000000000)
  directionHi := (286437039164024324797/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree093.table
  base := (4494064257210250780895997900924828497531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (10)
      previous := (0)
      next := (5)
      square := (641637059747847682267263280000000000000)
      linear := (-80630616011490138933526239320000000000000)
      constant := (2537139399298872374024162787420924828497531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree093.table
  base := (449406424595994743658237452246132352907/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (1365)
      previous := (0)
      next := (663)
      square := (86749330477909006642533995456000000000000)
      linear := (-11004691178784819830194230396800000000000000)
      constant := (349550905094933493235090763868336770941130264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71609259791006081199/25000000000000000000)
  centralHi := (286437039164024324797/100000000000000000000)
  directionLo := (35998694351582626873/12500000000000000000)
  directionHi := (57597910962532202997/20000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree094.table
  base := (4791033490188746408841296928534988755203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-733375188820385422588943313240000000000000)
      constant := (23323277561094590051199199267076814898796827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree094.table
  base := (4791033481102257686460631954352054660309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-55607345618294640541834361568800000000000000)
      constant := (1785186796417312666839450299965141988950368884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35998694351582626873/12500000000000000000)
  centralHi := (57597910962532202997/20000000000000000000)
  directionLo := (18095859112538590477/6250000000000000000)
  directionHi := (289533745800617447633/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree095.table
  base := (5091117176837465831387523908745226854017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-741074833537359594776150472600000000000000)
      constant := (23817461655060343531790479905178707041686153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree095.table
  base := (5091117169499443873721736155098814193771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-56191235342665181932697571153600000000000000)
      constant := (1823014175429453720342506283763346798394989196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18095859112538590477/6250000000000000000)
  centralHi := (289533745800617447633/100000000000000000000)
  directionLo := (58213948924112145239/20000000000000000000)
  directionHi := (72767436155140181549/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree096.table
  base := (84286176156521605907260589934707218271/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (10)
      previous := (0)
      next := (5)
      square := (641637059747847682267263280000000000000)
      linear := (-83197164250481529662595292440000000000000)
      constant := (2701867430577651174617452999035821261969344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree096.table
  base := (5394315268092032795391814579183887351729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-56775125067035723323560780738400000000000000)
      constant := (1861236662481982422799411432895528307849768804) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58213948924112145239/20000000000000000000)
  centralHi := (72767436155140181549/25000000000000000000)
  directionLo := (292597680287490177701/100000000000000000000)
  directionHi := (146298840143745088851/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree097.table
  base := (356289233731632185277016923179574234589/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (90)
      previous := (0)
      next := (45)
      square := (5774733537730629140405369520000000000000)
      linear := (-756474122971307939150564791320000000000000)
      constant := (24821313221131939729939026136217858689780816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree097.table
  base := (5700627734921994684324371221690400630277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6825)
      previous := (0)
      next := (3315)
      square := (433746652389545033212669977280000000000000)
      linear := (-57359014791406264714423990323200000000000000)
      constant := (1899854257546535146087574716062362710826067252) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell230.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292597680287490177701/100000000000000000000)
  centralHi := (146298840143745088851/50000000000000000000)
  directionLo := (73529419616301455457/25000000000000000000)
  directionHi := (294117678465205821829/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree098.table
  base := (1202010906589225132890579231617500287091/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18000000000000000000000000000000000000000
      center := (18)
      previous := (0)
      next := (9)
      square := (1154946707546125828081073904000000000000)
      linear := (-152834753537656422267554390136000000000000)
      constant := (5066196138498192635280398135740557502583819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree098.table
  base := (1202010905816768302689704635183928084673/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (1365)
      previous := (0)
      next := (663)
      square := (86749330477909006642533995456000000000000)
      linear := (-11588580903155361221057439981600000000000000)
      constant := (387773392119091956060139243283784335385238948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell230.Kernel098
