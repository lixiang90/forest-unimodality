import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell134.Parameters
import ForestUnimodality.BinomialMassData.Q23557_44732.Batch000_049
import ForestUnimodality.BinomialMassData.Q23557_44732.Batch050_099
import ForestUnimodality.BinomialMassData.Q23557_44732.Batch100_149
import ForestUnimodality.BinomialMassData.Q23557_44732.Batch150_199
import ForestUnimodality.BinomialMassData.Q11791_22366.Batch000_049
import ForestUnimodality.BinomialMassData.Q11791_22366.Batch050_099
import ForestUnimodality.BinomialMassData.Q11791_22366.Batch100_149
import ForestUnimodality.BinomialMassData.Q11791_22366.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree000.table
  base := (1758823786915484119552743881/20000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (78778877705394084046686131250000000000)
      linear := (-5253059923130389214165902875000000000)
      constant := (109926486682217757472046492562500000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree000.table
  base := (1758823786915484119552743881/20000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (78778877705394084046686131250000000000)
      linear := (-5253059923130389214165902875000000000)
      constant := (109926486682217757472046492562500000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree001.table
  base := (240452107681625559432180888654069698569989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-44134469057114353103777001144873411000000000000)
      constant := (30083130805819323215328307310940909145484355075621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree001.table
  base := (120120576085829929376986769598596594791567/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-22089259133291662102935852847580924250000000000)
      constant := (15028386747949991128118303265930716442273430529263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (9985209535862424591/20000000000000000000)
  directionHi := (12481511919828030739/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree002.table
  base := (55890953912827681182165237126855863905247/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-171282316311072886371150409581324597000000000000)
      constant := (35041439980811676320576365780242003752218671193915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree002.table
  base := (279029385197965941812278914128585515151063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-171458513148948770779529227782478347000000000000)
      constant := (34988433181722278839841850402001910786593696586807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9985209535862424591/20000000000000000000)
  centralHi := (12481511919828030739/25000000000000000000)
  directionLo := (7060609374376899231/10000000000000000000)
  directionHi := (70606093743768992311/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree003.table
  base := (87433108952367231846180588336715854428897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-127147847253958533267373408436451186000000000000)
      constant := (11036854607479264992966760473717716830763745653633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree003.table
  base := (87268226974311399621071462514692981381467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-127279994882365446573657522087316498500000000000)
      constant := (11016447845041261123620266946962401113952777090363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7060609374376899231/10000000000000000000)
  centralHi := (70606093743768992311/100000000000000000000)
  directionLo := (86474451201674834651/100000000000000000000)
  directionHi := (21618612800418708663/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree004.table
  base := (118327248903473171250674728699422571689593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-337309072704761246698343224164480147000000000000)
      constant := (15158751642774715419971889573609890473566367197977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree004.table
  base := (2361826758134148709133677431369258476179/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-168830733190256507757550430283393823500000000000)
      constant := (7565001597283383418320237730553319902496610313275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86474451201674834651/100000000000000000000)
  centralHi := (21618612800418708663/25000000000000000000)
  directionLo := (99852095358624245911/100000000000000000000)
  directionHi := (12481511919828030739/12500000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree005.table
  base := (42992466455800965016571098591135645054821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-210161225450802713430969815728028961000000000000)
      constant := (5656766035617141580139047002519676466178791246469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree005.table
  base := (42909092636565237492968526794205171518609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-210381471498147568941443338479471148500000000000)
      constant := (5646926934870582323219377426912001341274595530801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99852095358624245911/100000000000000000000)
  centralHi := (12481511919828030739/12500000000000000000)
  directionLo := (55819018229418763871/50000000000000000000)
  directionHi := (111638036458837527743/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree006.table
  base := (16529331936669049022684855867158903911097/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-125833957274612401756384009686908924250000000000)
      constant := (2268027600228293442437282727970477825421892249433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree006.table
  base := (32998209357898060306425047561900259192371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-251932209806038630125336246675548473500000000000)
      constant := (4529339151834415988811589923802310387065469958419) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55819018229418763871/50000000000000000000)
  centralHi := (111638036458837527743/100000000000000000000)
  directionLo := (30573335422044734467/25000000000000000000)
  directionHi := (122293341688178937869/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree007.table
  base := (52917796720108206452598434193660088342981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-586349207295293787189132446039213472000000000000)
      constant := (7708311614727949479595129658663131201243060596709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree007.table
  base := (26413016416589404337728265203840258815333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-293482948113929691309229154871625798500000000000)
      constant := (3849565392318871009095627749248683644573290344837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30573335422044734467/25000000000000000000)
  centralHi := (122293341688178937869/100000000000000000000)
  directionLo := (132091906103813309789/100000000000000000000)
  directionHi := (13209190610381330979/10000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree008.table
  base := (43469440132709923494742616192936331885197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-669362585492137967352728853330791247000000000000)
      constant := (6857349726833900589648800855091428101097143484333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree008.table
  base := (43396179332532130943249739498893075370171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-670067372843641504986244126135406247000000000000)
      constant := (6851182112600506548250429705543904547432071102619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132091906103813309789/100000000000000000000)
  centralHi := (13209190610381330979/10000000000000000000)
  directionLo := (141212187487537984621/100000000000000000000)
  directionHi := (70606093743768992311/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree009.table
  base := (36274452715452018806298562126784968113391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-752375963688982147516325260622369022000000000000)
      constant := (6331909975664711762833134135577649545016972517199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree009.table
  base := (36213319589939928841629243902483095168609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-753168849459423627354029942527560897000000000000)
      constant := (6328051110448407597618198249009659110924610380801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141212187487537984621/100000000000000000000)
  centralHi := (70606093743768992311/50000000000000000000)
  directionLo := (149778143037936368867/100000000000000000000)
  directionHi := (37444535759484092217/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree010.table
  base := (30537542906285255902260053285701365292349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-835389341885826327679921667913946797000000000000)
      constant := (6032533604864493691493095626488906845063501549661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree010.table
  base := (30484845930774785455123451480961110501489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-836270326075205749721815758919715547000000000000)
      constant := (6030614667415062141455727622163780553188748079121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149778143037936368867/100000000000000000000)
  centralHi := (37444535759484092217/25000000000000000000)
  directionLo := (39470006309197521287/25000000000000000000)
  directionHi := (157880025236790085149/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree011.table
  base := (12907856399089207550066747732071154641701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-459201360041335253921759037602762286000000000000)
      constant := (2951909761275926267544647095353302336818605150789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree011.table
  base := (2576933806221867896465356700383473291477/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-459685901345493936044800787655935098500000000000)
      constant := (2951834493623209000539086621372626777886308376265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39470006309197521287/25000000000000000000)
  centralHi := (157880025236790085149/100000000000000000000)
  directionLo := (33117193483534453391/20000000000000000000)
  directionHi := (41396491854418066739/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree012.table
  base := (10923153511649821290137250480941030798191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-500708049139757344003557241248551173500000000000)
      constant := (2956460091321314808507152270361313495255028584399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree012.table
  base := (21805024538477958856017120649645109050283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-1002473279306769994457387391704024847000000000000)
      constant := (5914477066696730043734786992344512683177667285387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33117193483534453391/20000000000000000000)
  centralHi := (41396491854418066739/25000000000000000000)
  directionLo := (86474451201674834651/50000000000000000000)
  directionHi := (172948902403349669303/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree013.table
  base := (4615489104661212946151189048654482306891/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-271107369119089717042677722447170030500000000000)
      constant := (1509726120784294041850770989425580146828079638699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree013.table
  base := (18425012921094735051805210852516352145019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-1085574755922552116825173208096179497000000000000)
      constant := (6042167422694490588326641197081819699400130035291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86474451201674834651/50000000000000000000)
  centralHi := (172948902403349669303/100000000000000000000)
  directionLo := (180010924889019767617/100000000000000000000)
  directionHi := (90005462444509883809/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree014.table
  base := (15547992077471779132866369351389549118067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-1167442854673203048334307297080257897000000000000)
      constant := (6267431989154116048205270003549697860645859687763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree014.table
  base := (1551488338076715382660741951317999098849/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-584338116269167119596479512244167073500000000000)
      constant := (3136215384927871290600581327093154160522582140805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180010924889019767617/100000000000000000000)
  centralHi := (90005462444509883809/50000000000000000000)
  directionLo := (7472246603669047951/4000000000000000000)
  directionHi := (23350770636465774847/12500000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree015.table
  base := (6510353467597783459329120892345363553573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-625228116435023614248951852185917836000000000000)
      constant := (3294017168985388478760314626184521522216563504197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree015.table
  base := (2598211202797214886533490895530657185913/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-1251777709154116361560744840880488797000000000000)
      constant := (6594814648156963573614871570346187812522288892285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7472246603669047951/4000000000000000000)
  centralHi := (23350770636465774847/12500000000000000000)
  directionLo := (193362751203933306243/100000000000000000000)
  directionHi := (48340687800983326561/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree016.table
  base := (10815922708035708156442608851895347711719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-1333469611066891408661500111663413447000000000000)
      constant := (6992685426212671703576878467751266518304897451591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree016.table
  base := (5394708637528818404485769357742314984877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-667439592884949241964265328636321723500000000000)
      constant := (3500650525167850637949938084086621381685760347853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193362751203933306243/100000000000000000000)
  centralHi := (48340687800983326561/25000000000000000000)
  directionLo := (199704190717248491823/100000000000000000000)
  directionHi := (12481511919828030739/6250000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree017.table
  base := (8882709147885224974921734746307160702839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-1416482989263735588825096518954991222000000000000)
      constant := (7475015943076898416455215042853932450412926189271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree017.table
  base := (4429535706883352332197735669641598506451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-708990331192840303148158236832399048500000000000)
      constant := (3742762489938889551711414324578514959359925263539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199704190717248491823/100000000000000000000)
  centralHi := (12481511919828030739/6250000000000000000)
  directionLo := (4117007361028547207/2000000000000000000)
  directionHi := (205850368051427360351/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree018.table
  base := (7179726521350055533030142671276763672119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-1499496367460579768988692926246568997000000000000)
      constant := (8029855962629799486677591233946709663408965687191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree018.table
  base := (7158699666583420300221754008233527675877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-1501082139001462728664102290056952747000000000000)
      constant := (8042319133330041216139402715436820084812535246853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4117007361028547207/2000000000000000000)
  centralHi := (205850368051427360351/100000000000000000000)
  directionLo := (52954570307826744233/25000000000000000000)
  directionHi := (211818281231306976933/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree019.table
  base := (5672941854031880463137151107941124294247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-1582509745657423949152289333538146772000000000000)
      constant := (8652949338483971011669310869558843473699015459783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree019.table
  base := (1130856949677453807785196368090557063267/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-1584183615617244851031888106449107397000000000000)
      constant := (8667429326398148745061396507455240353287558452815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52954570307826744233/25000000000000000000)
  centralHi := (211818281231306976933/100000000000000000000)
  directionLo := (217622596484514909267/100000000000000000000)
  directionHi := (54405649121128727317/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree020.table
  base := (4334095050372477938805914155102236187913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-1665523123854268129315885740829724547000000000000)
      constant := (9340761877529810600067535310514766715417707756457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree020.table
  base := (4317580742778754663020020504663660711539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-1667285092233026973399673922841262047000000000000)
      constant := (9357323139210843973372311082179393715454443743571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217622596484514909267/100000000000000000000)
  centralHi := (54405649121128727317/25000000000000000000)
  directionLo := (55819018229418763871/25000000000000000000)
  directionHi := (44655214583535011097/20000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree021.table
  base := (1569798998519864541434820748379065361503/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-874268251025556154739741074060651161000000000000)
      constant := (5045171831183764688903265996062562334344665451967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree021.table
  base := (3125013699844683784815648334272472458083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-1750386568848809095767459739233416697000000000000)
      constant := (10109052425638271341649678546666346004374433899587) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55819018229418763871/25000000000000000000)
  centralHi := (44655214583535011097/20000000000000000000)
  directionLo := (1429936829002638469/625000000000000000)
  directionHi := (228789892640422155041/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree022.table
  base := (12935633447935309405156561216632252747/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-228943735030994561205384819426610012125000000000)
      constant := (1362403106291625175625747980910806548339173325660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree022.table
  base := (1028424412042180831520103276220002406077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-916744022732295609067622777812785673500000000000)
      constant := (5460074581119797233202476492306609931982760114653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1429936829002638469/625000000000000000)
  centralHi := (228789892640422155041/100000000000000000000)
  directionLo := (117086960430370771497/50000000000000000000)
  directionHi := (46834784172148308599/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree023.table
  base := (1107839328288626262179114278902412670417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-1914563258444800669806674962704457872000000000000)
      constant := (11765333732697483279593926812209598674804475436913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree023.table
  base := (13706689732016835193470210349605094823/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-239573690260046667562878921502215749625000000000)
      constant := (1473567937162383843799223631542054923978609254470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117086960430370771497/50000000000000000000)
  centralHi := (46834784172148308599/20000000000000000000)
  directionLo := (59859228323714731243/25000000000000000000)
  directionHi := (239436913294858924973/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree024.table
  base := (120050556276066251821599580197117425697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-998788318320822424985135684998017823500000000000)
      constant := (6343465315063737301800712551802074963530662288833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree024.table
  base := (230176846421460473024330982901514079103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-1999690998696155462870817188409880647000000000000)
      constant := (12712497614555730109237448026613925316058926758367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59859228323714731243/25000000000000000000)
  centralHi := (239436913294858924973/100000000000000000000)
  directionLo := (244586683376357875737/100000000000000000000)
  directionHi := (122293341688178937869/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree025.table
  base := (-272601271690373974666522988294823446933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-1040295007419244515066933888643806711000000000000)
      constant := (6831276845630598023223569568854220384318840402763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree025.table
  base := (-276950377330565228735142055996475543429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-1041396237655968792619301502401017648500000000000)
      constant := (6845275748354807712403611164138709157737771952219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244586683376357875737/100000000000000000000)
  centralHi := (122293341688178937869/50000000000000000000)
  directionLo := (249630238396560614779/100000000000000000000)
  directionHi := (12481511919828030739/5000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree026.table
  base := (-1257898250538568030861610993907775380733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-2163603393035333210297464184579191197000000000000)
      constant := (14690974005144815013781572793625261244758750574563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree026.table
  base := (-12655100470789774369606681403584377917/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-541473487981929926901597205298547486750000000000)
      constant := (3680369501807615513497486569552286722482927389675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249630238396560614779/100000000000000000000)
  centralHi := (12481511919828030739/5000000000000000000)
  directionLo := (254573891353376285057/100000000000000000000)
  directionHi := (127286945676688142529/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree027.table
  base := (-1906249034679717999892465141658260780593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-2246616771232177390461060591870768972000000000000)
      constant := (15771158201999393382357865240371628497525298303023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree027.table
  base := (-1912900533404372473206343509506231752841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-2248995428543501829974174637586344597000000000000)
      constant := (15804245467542074972736429969266711783674130241751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254573891353376285057/100000000000000000000)
  centralHi := (127286945676688142529/50000000000000000000)
  directionLo := (259423353605024503953/100000000000000000000)
  directionHi := (129711676802512251977/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree028.table
  base := (-2497204403016505359967050521474949990521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-2329630149429021570624656999162346747000000000000)
      constant := (16902237180004158161272258038394127568884888896231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree028.table
  base := (-2503008993938203760444541022370271601927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-2332096905159283952341960453978499247000000000000)
      constant := (16937986367444719837229232572460134930671797964697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259423353605024503953/100000000000000000000)
  centralHi := (129711676802512251977/50000000000000000000)
  directionLo := (264183812207626619579/100000000000000000000)
  directionHi := (13209190610381330979/5000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree029.table
  base := (-1518304952619928499238886747201059749999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-1206321763812932875394126703226962261000000000000)
      constant := (9041739948850918963025548152850105867344157309489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree029.table
  base := (-3041669127552650107876835943481959186921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-2415198381775066074709746270370653897000000000000)
      constant := (18121971147538462089272976587212079391364804256631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264183812207626619579/100000000000000000000)
  centralHi := (13209190610381330979/5000000000000000000)
  directionLo := (67214998730487730297/25000000000000000000)
  directionHi := (268859994921950921189/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree030.table
  base := (-176469149066999838303359861966287530011/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-623914226455677482737962453436375574250000000000)
      constant := (4828567845640016779234352192372046146348760878105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree030.table
  base := (-353378743767560699710425301167776106313/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-1249149929195424098538766043381404273500000000000)
      constant := (9677793101505916185796614478903649101890432729715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67214998730487730297/25000000000000000000)
  centralHi := (268859994921950921189/100000000000000000000)
  directionLo := (273456225210376994529/100000000000000000000)
  directionHi := (27345622521037699453/10000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree031.table
  base := (-795932127876990465180713138168797738101/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-2578670284019554111115446221037080072000000000000)
      constant := (20594094262463869317137510722269852637018665548055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree031.table
  base := (-796698183193389743418565377304275285479/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-2581401335006630319445317903154963197000000000000)
      constant := (20638315414396739543807659051364466183413335698845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273456225210376994529/100000000000000000000)
  centralHi := (27345622521037699453/10000000000000000000)
  directionLo := (277976469045826556927/100000000000000000000)
  directionHi := (271461395552564997/97656250000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree032.table
  base := (-4390923539316534865893504340895935962017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-2661683662216398291279042628328657847000000000000)
      constant := (21922513247859538849757316600308938150413430570687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree032.table
  base := (-4394251108094808686179190804699268443163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-2664502811622412441813103719547117847000000000000)
      constant := (21969724631965886677035264285323158193824209676293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277976469045826556927/100000000000000000000)
  centralHi := (271461395552564997/97656250000000000)
  directionLo := (141212187487537984621/50000000000000000000)
  directionHi := (282424374975075969243/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree033.table
  base := (-2383050143541165773608264904994679618041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-1372348520206621235721319517810117811000000000000)
      constant := (11649581044391894051818377708888866443186577358951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree033.table
  base := (-4768988372900506702747247785230228102137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-2747604288238194564180889535939272497000000000000)
      constant := (23349448637134881685204570722299326952193306972007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141212187487537984621/50000000000000000000)
  centralHi := (282424374975075969243/100000000000000000000)
  directionLo := (35850413573481631629/12500000000000000000)
  directionHi := (286803308587853053033/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree034.table
  base := (-5107655115287661245740185089521857863717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-2827710418610086651606235442911813397000000000000)
      constant := (24723732609566218761477777816486521674232920339387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree034.table
  base := (-5110159516730741952366777996757223763843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-2830705764853976686548675352331427147000000000000)
      constant := (24777180182957434411331505480560149012035137743773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35850413573481631629/12500000000000000000)
  centralHi := (286803308587853053033/100000000000000000000)
  directionLo := (291116382317821839579/100000000000000000000)
  directionHi := (14555819115891091979/5000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree035.table
  base := (-5417661608941679776120519911061150772523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-2910723796806930831769831850203391172000000000000)
      constant := (26195965488725187736778119506246858416011318379253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree035.table
  base := (-541983146587589502711135913116716260917/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-1456903620734879404458230584361790898500000000000)
      constant := (13126330390343934596477914741778224157758646542935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291116382317821839579/100000000000000000000)
  centralHi := (14555819115891091979/5000000000000000000)
  directionLo := (295366481325645953257/100000000000000000000)
  directionHi := (147683240662822976629/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree036.table
  base := (-2848932352549439808815028032339316713407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-1496868587501887505966714128747484473500000000000)
      constant := (13857821252662161517462807910125524560712161130977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree036.table
  base := (-5699743209240625725644155879475194717749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-2996908718085540931284246985115736447000000000000)
      constant := (27775672953262392605937884471907027302422810829739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295366481325645953257/100000000000000000000)
  centralHi := (147683240662822976629/50000000000000000000)
  directionLo := (59911257215174547547/20000000000000000000)
  directionHi := (37444535759484092217/12500000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree037.table
  base := (-1487433209178442107353734659041180849283/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-769187638300154798024256166196636680500000000000)
      constant := (7320645004472175791955215919437570752000832003613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree037.table
  base := (-5951357884039772244399349971055003450283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-3080010194701323053652032801507891097000000000000)
      constant := (29346033721488580102213930056403276841614371114613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59911257215174547547/20000000000000000000)
  centralHi := (37444535759484092217/12500000000000000000)
  directionLo := (303688292109602168103/100000000000000000000)
  directionHi := (37961036513700271013/12500000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree038.table
  base := (-246980071646939627403289316869771560219/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-3159763931397463372260621072078124497000000000000)
      constant := (30896623479479179202425389506009044414306978297725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree038.table
  base := (-6175906576780639058879455664845102744819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-3163111671317105176019818617900045747000000000000)
      constant := (30963589126316913389310208785607132697580438462509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303688292109602168103/100000000000000000000)
  centralHi := (37961036513700271013/12500000000000000000)
  directionLo := (307764827427248420933/100000000000000000000)
  directionHi := (153882413713624210467/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree039.table
  base := (-1274642320546735915402060733354597474587/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-3242777309594307552424217479369702272000000000000)
      constant := (32557642823943199156328916315317539737512296469785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree039.table
  base := (-1274885032004001309922341660208737885047/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-3246213147932887298387604434292200397000000000000)
      constant := (32628209622054772389352759057290667216805407195085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307764827427248420933/100000000000000000000)
  centralHi := (153882413713624210467/50000000000000000000)
  directionLo := (311788067825247201697/100000000000000000000)
  directionHi := (155894033912623600849/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree040.table
  base := (-6546737587351711069700826821983052323739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-3325790687791151732587813886661280047000000000000)
      constant := (34265528584714420045629982371633606639732938090629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree040.table
  base := (-6547785274240151527501616215256165124851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-3329314624548669420755390250684355047000000000000)
      constant := (34339786201788851850813188371717828365386512738861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311788067825247201697/100000000000000000000)
  centralHi := (155894033912623600849/50000000000000000000)
  directionLo := (39470006309197521287/12500000000000000000)
  directionHi := (315760050473580170297/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree041.table
  base := (-6695816451537008259641824199593402147237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-3408804065987995912751410293952857822000000000000)
      constant := (36020188629653230444196997972500293243570038018107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree041.table
  base := (-3348360193499109406745884835280075150123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-1706208050582225771561588033538254848500000000000)
      constant := (18049113569220628582042709946125876680844019332853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39470006309197521287/12500000000000000000)
  centralHi := (315760050473580170297/100000000000000000000)
  directionLo := (159841342987315741073/50000000000000000000)
  directionHi := (319682685974631482147/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree042.table
  base := (-6821068258313163677478747163570441907739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-3491817444184840092915006701244435597000000000000)
      constant := (37821545413994752075203226130165607918513975514629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree042.table
  base := (-6821847712740879086576385430878686648331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-3495517577780233665490961883468664347000000000000)
      constant := (37903455243488684276303153836440992975768602437141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159841342987315741073/50000000000000000000)
  centralHi := (319682685974631482147/100000000000000000000)
  directionLo := (161778884552984688611/50000000000000000000)
  directionHi := (323557769105969377223/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree043.table
  base := (-865376863578474780226530360777480508449/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-446853852797710534134825388567001671500000000000)
      constant := (4958691708634145856350344914273963539327782877439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree043.table
  base := (-1730921662935352048278048489317705104619/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-894654763599003946964686924965204749250000000000)
      constant := (9938851390249592712441243745278692121213656320309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161778884552984688611/50000000000000000000)
  centralHi := (323557769105969377223/100000000000000000000)
  directionLo := (327386988418459811859/100000000000000000000)
  directionHi := (16369349420922990593/5000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree044.table
  base := (-3501047845862836966993268789476781770577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-1828922100289264226621099757913795573500000000000)
      constant := (20782049228800000820841030530739504690907125144847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree044.table
  base := (-700267430166819294202271917934375474387/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-1830860265505898955113266758126486823500000000000)
      constant := (20827011713879632669346283391778565547195145958785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327386988418459811859/100000000000000000000)
  centralHi := (16369349420922990593/5000000000000000000)
  directionLo := (33117193483534453391/10000000000000000000)
  directionHi := (331171934835344533911/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree045.table
  base := (-1764670092478976997683729122589646777533/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-935214394693843158351448980779792230500000000000)
      constant := (10876298384322456696543543672386996145279976339363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree045.table
  base := (-7059178507118710682815644847269066874927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-3744822007627580032594319332645128297000000000000)
      constant := (43599262841313975815067423912398019691114802467697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33117193483534453391/10000000000000000000)
  centralHi := (331171934835344533911/100000000000000000000)
  directionLo := (167457054688256291613/50000000000000000000)
  directionHi := (334914109376512583227/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree046.table
  base := (-1773270047282983552359159620186001199701/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-955967739243054203392348082602686674250000000000)
      constant := (11373194995971313431390880136532414183012005987211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree046.table
  base := (-7093508838359348773825016392118392306967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-3827923484243362154962105149037282947000000000000)
      constant := (45591085086963178281980230754724830817589175840137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167457054688256291613/50000000000000000000)
  centralHi := (334914109376512583227/100000000000000000000)
  directionLo := (338614930114340323423/100000000000000000000)
  directionHi := (10581716566073135107/3125000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree047.table
  base := (-7105557144453201589775807904748660610883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-3906884335169060993732988737702324472000000000000)
      constant := (47526825032415526053548043379210217223943544181213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree047.table
  base := (-7105925828242245791220588921529086811779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-3911024960859144277329890965429437597000000000000)
      constant := (47629457582601516576538010159521296763682279079069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338614930114340323423/100000000000000000000)
  centralHi := (10581716566073135107/3125000000000000000)
  directionLo := (342275738452518028681/100000000000000000000)
  directionHi := (171137869226259014341/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree048.table
  base := (-7096331777442878777824213662379773635589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-3989897713365905173896585144993902247000000000000)
      constant := (49607301102065450638029183411638891141197567445979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree048.table
  base := (-7096648743932617656599535432514605912847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-3994126437474926399697676781821592247000000000000)
      constant := (49714352906789354317011155607936316255502975644817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342275738452518028681/100000000000000000000)
  centralHi := (171137869226259014341/50000000000000000000)
  directionLo := (86474451201674834651/25000000000000000000)
  directionHi := (69179560961339867721/20000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree049.table
  base := (-7065589738171766348514888581064717112417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-4072911091562749354060181552285480022000000000000)
      constant := (51734184975532040345284909348797386001866574425087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree049.table
  base := (-7065862126085245775442007368344848074851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-4077227914090708522065462598213746897000000000000)
      constant := (51845747980966704815423617560831943301976500188861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86474451201674834651/25000000000000000000)
  centralHi := (69179560961339867721/20000000000000000000)
  directionLo := (349482333755184860691/100000000000000000000)
  directionHi := (87370583438796215173/25000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree050.table
  base := (-3506743653907560776737861278041791660397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-2077962234879796767111888979788528898500000000000)
      constant := (26953728554185688591991546431116854976806289642867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree050.table
  base := (-876715161390442920021827079118026344041/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-520041173838311330554156051825737693375000000000)
      constant := (6752952922667627838474184435437759457850694344951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349482333755184860691/100000000000000000000)
  centralHi := (87370583438796215173/25000000000000000000)
  directionLo := (353030468718844961553/100000000000000000000)
  directionHi := (176515234359422480777/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree051.table
  base := (-69401560466092277846694050605214339289/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-1059734461989109428596843591717158893000000000000)
      constant := (14031775261931884708466423324844541482669875916975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree051.table
  base := (-6940356961179360829547494076573292718177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-4243430867322272766801034230998056197000000000000)
      constant := (56247962759869297790127401993129987338617363368447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353030468718844961553/100000000000000000000)
  centralHi := (176515234359422480777/50000000000000000000)
  directionLo := (71308659244365075449/20000000000000000000)
  directionHi := (178271648110912688623/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree052.table
  base := (-684570670580015078321943138326798522897/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-2160975613076640947275485387080106673500000000000)
      constant := (29196551471553143100043700026754149318102731901835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree052.table
  base := (-6845879160106315981937120836166387712211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-4326532343938054889168820047390210847000000000000)
      constant := (58518752357024618809759129329112536527735013279821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71308659244365075449/20000000000000000000)
  centralHi := (178271648110912688623/50000000000000000000)
  directionLo := (72004369955607907047/20000000000000000000)
  directionHi := (90005462444509883809/25000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree053.table
  base := (-1346046504044023221516048459666884874071/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7835696)
      previous := (3917848)
      next := (3917848)
      square := (28058515314574800126740105995050000000000000)
      linear := (-1568161126504138866042921744909858000000000000)
      constant := (21611054159703504504654738743910823967607425045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree053.table
  base := (-6730380491994326919536640064622192611763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7835696)
      previous := (3917848)
      next := (3917848)
      square := (28058515314574800126740105995050000000000000)
      linear := (-1569823360823722681216306822279233000000000000)
      constant := (21657522460586266037300296628495679362731699477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72004369955607907047/20000000000000000000)
  centralHi := (90005462444509883809/25000000000000000000)
  directionLo := (181733556721425427813/50000000000000000000)
  directionHi := (363467113442850855627/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree054.table
  base := (-412113248726572692800195693525162835273/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-560997247818371281859770448592921112125000000000)
      constant := (7883016975792666335178004739758497809107934889006) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree054.table
  base := (-824242362515611006489289128685064736879/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-561591912146202391738048960021815018375000000000)
      constant := (7899954714576118822895331278673555844948992805169) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181733556721425427813/50000000000000000000)
  centralHi := (363467113442850855627/100000000000000000000)
  directionLo := (183440012532268406803/50000000000000000000)
  directionHi := (366880025064536813607/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree055.table
  base := (-1609127790341191446894999307921041008943/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-1142747840185953608760439999008736668000000000000)
      constant := (16367287173677321520421108153148161601417293989873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree055.table
  base := (-6436619988758196039390585766261516798649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-4575836773785401256272177496566674797000000000000)
      constant := (65609715527055750245538298771490560603796040169639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183440012532268406803/50000000000000000000)
  centralHi := (366880025064536813607/100000000000000000000)
  directionLo := (74052295853196100081/20000000000000000000)
  directionHi := (185130739632990250203/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree056.table
  base := (-312919284693117162998420177843141998257/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-1163501184735164653801339100831631111750000000000)
      constant := (16980120710712200923268409479569371393217703446635) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree056.table
  base := (-3129239488533129865037936512775878834411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-2329469125200591689319981656479414723500000000000)
      constant := (34033103558722892928127655885732143087442644724021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74052295853196100081/20000000000000000000)
  centralHi := (185130739632990250203/50000000000000000000)
  directionLo := (7472246603669047951/2000000000000000000)
  directionHi := (373612330183452397551/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree057.table
  base := (-6059482409371969578631271367918796460573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-4737018117137502795368952810618102222000000000000)
      constant := (70418132393942120293396042072600002997020731972803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree057.table
  base := (-6059562343527127330081478970628512100333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-4742039727016965501007749129350984097000000000000)
      constant := (70569106675204343208940042853526595321902038290163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7472246603669047951/2000000000000000000)
  centralHi := (373612330183452397551/100000000000000000000)
  directionLo := (376933393986239965299/100000000000000000000)
  directionHi := (3769333939862399653/1000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree058.table
  base := (-1459960183802686927209579749640524262893/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-1205007873833586743883137304477419999250000000000)
      constant := (18240523104307276586213657338393121664740499758323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree058.table
  base := (-2919954604921815264198141061304435141713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-2412570601816373811687767472871569373500000000000)
      constant := (36559204653895628681357267971571754518243729635343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376933393986239965299/100000000000000000000)
  centralHi := (3769333939862399653/1000000000000000000)
  directionLo := (23764090699886528573/6250000000000000000)
  directionHi := (380225451198184457169/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree059.table
  base := (-5599493864870471574843083705222130578439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-4903044873531191155696145625201257772000000000000)
      constant := (75552358761548639973588947685463415225744144242329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree059.table
  base := (-559955250566761218087213021671136127759/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-2454121340124264872871660381067646698500000000000)
      constant := (37857055448520547951058829151421395385565103724245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23764090699886528573/6250000000000000000)
  centralHi := (380225451198184457169/100000000000000000000)
  directionLo := (191744624419916853163/50000000000000000000)
  directionHi := (383489248839833706327/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree060.table
  base := (-133461743596320917921088793105384637731/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-623257281466004416982467754061604443375000000000)
      constant := (9773615991506319910838532243841251925909555102705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree060.table
  base := (-2669259974431904862145814781581714557127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-2495672078432155934055553289263724023500000000000)
      constant := (39178103988285929296093103691689610450741836071897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191744624419916853163/50000000000000000000)
  centralHi := (383489248839833706327/100000000000000000000)
  directionLo := (193362751203933306243/50000000000000000000)
  directionHi := (386725502407866612487/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree061.table
  base := (-1264197974888301587139197354281672256479/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-1267267907481219879005834609946103330500000000000)
      constant := (20217949246602705664933926509903349871508009320769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree061.table
  base := (-2528417435269987335565302983421916125787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-2537222816740046995239446197459801348500000000000)
      constant := (40522348814303566112415489642370824093908218057157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193362751203933306243/50000000000000000000)
  centralHi := (386725502407866612487/100000000000000000000)
  directionLo := (7798697954132953661/2000000000000000000)
  directionHi := (389934897706647683051/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree062.table
  base := (-4754480139873669073627903939004894575371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-5152085008121723696186934847075991097000000000000)
      constant := (83600963447463316729866711313952914079905230754581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree062.table
  base := (-1188629227359066085226842306026817760669/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-1289386777523969028211669552827939336750000000000)
      constant := (20944894349284027030473351114413564935304610561859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7798697954132953661/2000000000000000000)
  centralHi := (389934897706647683051/100000000000000000000)
  directionLo := (39311809254519276059/10000000000000000000)
  directionHi := (393118092545192760591/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree063.table
  base := (-886310228267593341075510335291798610389/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-5235098386318567876350531254367568872000000000000)
      constant := (86376425229650504049559459092894652344844207843895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree063.table
  base := (-4431582596368579171603001275078651799697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-5240648586711658235214464027703911997000000000000)
      constant := (86560845214823397021524692603017906182120962825167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39311809254519276059/10000000000000000000)
  centralHi := (393118092545192760591/100000000000000000000)
  directionLo := (396275718311439929369/100000000000000000000)
  directionHi := (39627571831143992937/10000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree064.table
  base := (-4088018944192028580920661882743724992217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-5318111764515412056514127661659146647000000000000)
      constant := (89198180577106403261584247589755424842516813002887) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree064.table
  base := (-817609169228113352361841590505794063249/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-5323750063327440357582249844096066647000000000000)
      constant := (89388499341490765219708887869747927322554231901195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396275718311439929369/100000000000000000000)
  centralHi := (39627571831143992937/10000000000000000000)
  directionLo := (399408381434496983647/100000000000000000000)
  directionHi := (12481511919828030739/3125000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree065.table
  base := (-372389536920608333681578731815990612187/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-2700562571356128118338862034475362211000000000000)
      constant := (46033114005765764993119948738876236035992983037785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree065.table
  base := (-465489796447409295469116765909865888327/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-675856442492902809993754457561027662125000000000)
      constant := (11532817289042255930212954302533539418197294315097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399408381434496983647/100000000000000000000)
  centralHi := (12481511919828030739/3125000000000000000)
  directionLo := (40251666474445698679/10000000000000000000)
  directionHi := (402516664744456986791/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree066.table
  base := (-1669595184282497465948278847495270645147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-2742069260454550208420660238121151098500000000000)
      constant := (47490283144155365351650078994526232211701215850117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree066.table
  base := (-3339210032027320384202564348851282487033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-5489953016559004602317821476880375947000000000000)
      constant := (95182960894360893953636483941460258652177003893863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40251666474445698679/10000000000000000000)
  centralHi := (402516664744456986791/100000000000000000000)
  directionLo := (16224045149536710019/4000000000000000000)
  directionHi := (101400282184604437619/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree067.table
  base := (-2933912321273072401068838114480700416873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-5567151899105944597004916883533879972000000000000)
      constant := (97941194359570008196061618470990760188878775642103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree067.table
  base := (-2933929126670514615370994406797229696403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-5573054493174786724685607293272530597000000000000)
      constant := (98149766049667368266842095506672233476552215681933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16224045149536710019/4000000000000000000)
  centralHi := (101400282184604437619/25000000000000000000)
  directionLo := (6385348636882712247/1562500000000000000)
  directionHi := (408662312760493583809/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree068.table
  base := (-2508068281849652274301157355211573440887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-5650165277302788777168513290825457747000000000000)
      constant := (100948111343074779097467381528436201609596700073257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree068.table
  base := (-2508082641435665207479775224810901923223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-5656155969790568847053393109664685247000000000000)
      constant := (101162952904601033562652726720599573529852614386953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6385348636882712247/1562500000000000000)
  centralHi := (408662312760493583809/100000000000000000000)
  directionLo := (4117007361028547207/1000000000000000000)
  directionHi := (411700736102854720701/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree069.table
  base := (-1030832094851524358429829793348191961591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-2866589327749816478666054849058517761000000000000)
      constant := (52000658248022837337828900811274567784147021913001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree069.table
  base := (-2061676456809726942935507226302534216169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-5739257446406350969421178926056839897000000000000)
      constant := (104222520723751196204814501944063411179520889322359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4117007361028547207/1000000000000000000)
  centralHi := (411700736102854720701/100000000000000000000)
  directionLo := (207358449517079826577/50000000000000000000)
  directionHi := (82943379806831930631/20000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree070.table
  base := (-1594705045401614456157119293306722936273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-5816192033696477137495706105408613297000000000000)
      constant := (107100809193114172028970880884241812399325119055503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree070.table
  base := (-389334844425569661112575755345937811/2441406250000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-727794865377766636473620592806124318375000000000)
      constant := (13416058611009572871934996144746343077429847447552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207358449517079826577/50000000000000000000)
  centralHi := (82943379806831930631/20000000000000000000)
  directionLo := (417711283761148017271/100000000000000000000)
  directionHi := (52213910470143502159/12500000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree071.table
  base := (-69199691192301626777191145361752885561/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-737400676486665164707412814087523884000000000000)
      constant := (13780823613470422509871095576284708893146806723342) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree071.table
  base := (-1107204006012340570374000179504733828597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-5905460399637915214156750558841149197000000000000)
      constant := (110480796876491263768760810558539089601314645593067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417711283761148017271/100000000000000000000)
  centralHi := (52213910470143502159/12500000000000000000)
  directionLo := (210342177664313955521/50000000000000000000)
  directionHi := (420684355328627911043/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree072.table
  base := (-599137775365193116945158266618121689257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-5982218790090165497822898919991768847000000000000)
      constant := (113438655196702868233920445643561330777401702790327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree072.table
  base := (-599145413920040311865162084086247248287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-5988561876253697336524536375233303847000000000000)
      constant := (113679504250364751914930374425177776771201571654657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210342177664313955521/50000000000000000000)
  centralHi := (420684355328627911043/100000000000000000000)
  directionLo := (52954570307826744233/12500000000000000000)
  directionHi := (84727312492522790773/20000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree073.table
  base := (-70536178598733052558177489879370991641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-6065232168287009677986495327283346622000000000000)
      constant := (116677007686713599400088083016787572820018953268551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree073.table
  base := (-70542698861558825094236406537255232889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-6071663352869479458892322191625458497000000000000)
      constant := (116924590640474998012572306797161147007112325666279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52954570307826744233/12500000000000000000)
  centralHi := (84727312492522790773/20000000000000000000)
  directionLo := (213284169180472206893/50000000000000000000)
  directionHi := (426568338360944413787/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree074.table
  base := (239303609316502088162180153224165620517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-3074122773241926929075045867287462198500000000000)
      constant := (59980823031786204194591113124732821906453223935813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree074.table
  base := (239300826989027155525064983305226208789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-3077382414742630790630054004008806573500000000000)
      constant := (60108027868013014845455564153479046847200559648821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213284169180472206893/50000000000000000000)
  centralHi := (426568338360944413787/100000000000000000000)
  directionLo := (429480101435321574721/100000000000000000000)
  directionHi := (214740050717660787361/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree075.table
  base := (262072575230072854698976434909319169801/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-1557814731170174509578422035466625543000000000000)
      constant := (30823142515681808924520269097259587781556967291689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree075.table
  base := (131035694084907039726039987994326163543/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-779733288262630462953486728051220974625000000000)
      constant := (15444237409425432237615190147784975443037018009527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429480101435321574721/100000000000000000000)
  centralHi := (214740050717660787361/50000000000000000000)
  directionLo := (86474451201674834651/20000000000000000000)
  directionHi := (54046532001046771657/12500000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree076.table
  base := (1638511287256665139377394651217776803611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-6314272302877542218477284549158079947000000000000)
      constant := (126669779461446323091340488301649260491775645014779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree076.table
  base := (1638507236364235930805446599010599618657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-6320967782716825825995679640801922447000000000000)
      constant := (126938121038392803374442318174674468615892839286273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86474451201674834651/20000000000000000000)
  centralHi := (54046532001046771657/12500000000000000000)
  directionLo := (87049038593805963707/20000000000000000000)
  directionHi := (54405649121128727317/12500000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree077.table
  base := (2249268678185156113794261875108134770153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-6397285681074386398640880956449657722000000000000)
      constant := (130093274072208348220283958471930994769973466631817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree077.table
  base := (562316305704741578735693464697605768423/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-1601017314833151987090866364298519274250000000000)
      constant := (32592180209907284331710946017825301052922432715847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87049038593805963707/20000000000000000000)
  centralHi := (54405649121128727317/12500000000000000000)
  directionLo := (438099290389204980279/100000000000000000000)
  directionHi := (10952482259730124507/2500000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree078.table
  base := (720140302824662587346799496402717606119/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-1620074764817807644701119340935308874250000000000)
      constant := (33390763434284330624756190978003235906032545413191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree078.table
  base := (2880558264402946717281704838051395327841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-6487170735948390070731251273586231747000000000000)
      constant := (133845698523083176278259302702316948146436782933249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438099290389204980279/100000000000000000000)
  centralHi := (10952482259730124507/2500000000000000000)
  directionLo := (27558432131535438939/6250000000000000000)
  directionHi := (17637396564182680921/4000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree079.table
  base := (706477564754750658907193888910651989073/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-6563312437468074758968073771032813272000000000000)
      constant := (137079118323317095307691894093550564219426514818485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree079.table
  base := (3532385310935123001982728429743584791613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-6570272212564172193099037089978386397000000000000)
      constant := (137369053957419814240979448222664211678067293265757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27558432131535438939/6250000000000000000)
  centralHi := (17637396564182680921/4000000000000000000)
  directionLo := (221876209130946960817/50000000000000000000)
  directionHi := (88750483652378784327/20000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree080.table
  base := (2102373810413167154539946174844253221499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-3323162907832459469565835089162195523500000000000)
      constant := (70320733859423210251558805504919173092467268754011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree080.table
  base := (4204745478452058744233968355357267412811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-6653373689179954315466822906370541047000000000000)
      constant := (140938787032091035561033260463821347035082495713579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221876209130946960817/50000000000000000000)
  centralHi := (88750483652378784327/20000000000000000000)
  directionLo := (55819018229418763871/12500000000000000000)
  directionHi := (446552145835350110969/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree081.table
  base := (979527969830542016684407344507893993913/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-6729339193861763119295266585615968822000000000000)
      constant := (144250101829517524388785893801799157400599644452285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree081.table
  base := (4897638022909146579055897947269737479237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-6736475165795736437834608722762695697000000000000)
      constant := (144554897654047001848150763325273585796317527329893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55819018229418763871/12500000000000000000)
  centralHi := (446552145835350110969/100000000000000000000)
  directionLo := (449334429113809106603/100000000000000000000)
  directionHi := (112333607278452276651/25000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree082.table
  base := (5611063874568409409788216623445814051899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-6812352572058607299458862992907546597000000000000)
      constant := (147905020576019621063717289948428091353519508419611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree082.table
  base := (5611062318042708569891260304268299315649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-6819576642411518560202394539154850347000000000000)
      constant := (148217385744967497560325531839713544760314113643361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449334429113809106603/100000000000000000000)
  centralHi := (112333607278452276651/25000000000000000000)
  directionLo := (28256224385073941083/6250000000000000000)
  directionHi := (452099590161183057329/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree083.table
  base := (793127395397630595809534113499185743731/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-861920743781931434952807425024890546500000000000)
      constant := (18950777986448050170432218877116006175448958813459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree083.table
  base := (6345017836734614435799765605403180144351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-6902678119027300682570180355547004997000000000000)
      constant := (151926251238931398681987746922621343848827482296639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28256224385073941083/6250000000000000000)
  centralHi := (452099590161183057329/100000000000000000000)
  directionLo := (454847941251564461459/100000000000000000000)
  directionHi := (22742397062578223073/5000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree084.table
  base := (443719079096168750770517261295568354563/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-872297416056536957473256975936337768375000000000)
      constant := (19419213965000454790665401811100693928147439196614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree084.table
  base := (709950413532523362871409818418669407179/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-3492889797821541402468983085969579823500000000000)
      constant := (77840747040227429263433660069572169319608693357655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454847941251564461459/100000000000000000000)
  centralHi := (22742397062578223073/5000000000000000000)
  directionLo := (1429936829002638469/312500000000000000)
  directionHi := (457579785280844310081/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree085.table
  base := (3937260901641771914911519181828569752183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-3530696353324569919974826107391139961000000000000)
      constant := (79573742006980047452798141918176794164746362614487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree085.table
  base := (1968630210102058415880973641271419592123/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-1767220268064716231826437997082828574250000000000)
      constant := (39870778555709967991253062331107021949495490805147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1429936829002638469/312500000000000000)
  centralHi := (457579785280844310081/100000000000000000000)
  directionLo := (18411816646253700103/4000000000000000000)
  directionHi := (28768463509771406411/6250000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree086.table
  base := (2167517114478679536549006811839127074793/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-1786101521211496005028312155518464424250000000000)
      constant := (40746885183405554136908875461034478617679677360777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree086.table
  base := (4335033818857276799976328591700658901489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-3575991274437323524836768902361734473500000000000)
      constant := (81665555813392055413360848087160806526683515679121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18411816646253700103/4000000000000000000)
  centralHi := (28768463509771406411/6250000000000000000)
  directionLo := (7234298736966707211/1562500000000000000)
  directionHi := (92599023833173852301/20000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree087.table
  base := (9486144961327137406725181111229676578079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-7227419463042828200276845029365435472000000000000)
      constant := (166873881845460918253666045936354142787864828341631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree087.table
  base := (4743072131377507746129207582125067123687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-3617542012745214586020661810557811798500000000000)
      constant := (83612743129605346836035550042679551848078996015943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7234298736966707211/1562500000000000000)
  centralHi := (92599023833173852301/20000000000000000000)
  directionLo := (465679171327529341307/100000000000000000000)
  directionHi := (116419792831882335327/25000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree088.table
  base := (2064550217569105362616460231271511189833/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-7310432841239672380440441436657013247000000000000)
      constant := (170806507321253365477474413516919038334291484876685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree088.table
  base := (10322750492943337323123294531564975756979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-7318185502106211294409109437507778247000000000000)
      constant := (171166238092283093813564798587527203474465181923731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465679171327529341307/100000000000000000000)
  centralHi := (116419792831882335327/25000000000000000000)
  directionLo := (117086960430370771497/25000000000000000000)
  directionHi := (468347841721483085989/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree089.table
  base := (174685728867459219138425760621071492207/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-924180777429564570075504730493573877750000000000)
      constant := (21848177142155524511556849088524419060067374217784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree089.table
  base := (11179886140965334939872244379043060409733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-7401286978721993416776895253899932897000000000000)
      constant := (175153367102575895098617351831434699601837339606437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117086960430370771497/25000000000000000000)
  centralHi := (468347841721483085989/100000000000000000000)
  directionLo := (471001391804788959287/100000000000000000000)
  directionHi := (58875173975598619911/12500000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree090.table
  base := (602877574023297322054166794345264906829/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-1869114899408340185191908562810042199250000000000)
      constant := (44702652818359825403421106567911674682838336751905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree090.table
  base := (12057551049197157878546086900002051815823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-7484388455337775539144681070292087547000000000000)
      constant := (179186873270376739333993612123717758304038346494447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471001391804788959287/100000000000000000000)
  centralHi := (58875173975598619911/12500000000000000000)
  directionLo := (118410018927592563861/25000000000000000000)
  directionHi := (94728015142074051089/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree091.table
  base := (6477872726067761904467021098063284281581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-3779736487915102460465615329265873286000000000000)
      constant := (91441044856505609213587050547305773927603751972109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree091.table
  base := (404867033906456166937445276504276696709/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-945936241494194707689058360835530274625000000000)
      constant := (22908344572387338782822640544511549147145142086804) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118410018927592563861/25000000000000000000)
  centralHi := (94728015142074051089/20000000000000000000)
  directionLo := (238132070265536795807/50000000000000000000)
  directionHi := (95252828106214718323/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree092.table
  base := (6937234224644183487971421580607479434879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-3821243177013524550547413532911662173500000000000)
      constant := (93499926220899245369024493210632220762203976516831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree092.table
  base := (13874468136797762074182036609050635044819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-7650591408569339783880252703076396847000000000000)
      constant := (187393017014785682749399120865002573267830556237491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238132070265536795807/50000000000000000000)
  centralHi := (95252828106214718323/20000000000000000000)
  directionLo := (59859228323714731243/12500000000000000000)
  directionHi := (95774765317943569989/20000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree093.table
  base := (7406860188317056963107845697923748852881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-3862749866111946640629211736557451061000000000000)
      constant := (95581949723942077282988181403665021676443134037809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree093.table
  base := (7406860055340760303101660308705314516359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-3866846442592560953124019259734275748500000000000)
      constant := (95782827282847964995146941205953995433000138680551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59859228323714731243/12500000000000000000)
  centralHi := (95774765317943569989/20000000000000000000)
  directionLo := (240734683847984454641/50000000000000000000)
  directionHi := (481469367695968909283/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree094.table
  base := (3154700230798391475379234975395810028091/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-7808513110420737461422019880406479897000000000000)
      constant := (195374230721240839124554728904832872542270680527495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree094.table
  base := (15773500927672713847978584617151489593301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-7816794361800904028615824335860706147000000000000)
      constant := (195784669221951608350875859486501920567127040883189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240734683847984454641/50000000000000000000)
  centralHi := (481469367695968909283/100000000000000000000)
  directionLo := (60506373923852159069/12500000000000000000)
  directionHi := (484050991390817272553/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree095.table
  base := (8376905356950655554528157910732838662993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-3945763244308790820792808143849028836000000000000)
      constant := (99815423126715978986802254842204797643400847790577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree095.table
  base := (16753810521330803695011288861225821691741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-7899895838416686150983610152252860797000000000000)
      constant := (200050060975243698086911686225750425889374244980349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60506373923852159069/12500000000000000000)
  centralHi := (484050991390817272553/100000000000000000000)
  directionLo := (486618919179382096421/100000000000000000000)
  directionHi := (243309459589691048211/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree096.table
  base := (4438662249902525939436081580254323303007/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-1993634966703606455437303173747408861750000000000)
      constant := (50983436509340031517133325510153268640314847583423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree096.table
  base := (1775464883577380704875198951267220764579/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-3991498657516234136675697984322507723500000000000)
      constant := (102180914909291813473895066271084456312342195200655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486618919179382096421/100000000000000000000)
  centralHi := (243309459589691048211/50000000000000000000)
  directionLo := (19566934670108630059/4000000000000000000)
  directionHi := (122293341688178937869/25000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree097.table
  base := (18776015963381023745760370893429560893101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-8057553245011270001912809102281213222000000000000)
      constant := (208282930067055339617262710497154767398660594685389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree097.table
  base := (18776015824006462518693464254130358338453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-8066098791648250395719181785037170097000000000000)
      constant := (208719975746094191558592935761938907187193821230517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19566934670108630059/4000000000000000000)
  centralHi := (122293341688178937869/25000000000000000000)
  directionLo := (3841519876556543053/781250000000000000)
  directionHi := (98342908839847502157/20000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree098.table
  base := (3963582313013093952342548691337382763577/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-8140566623208114182076405509572790997000000000000)
      constant := (212678398337496635055725358412579614956051737160765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree098.table
  base := (2477238930814114891962614728224689385839/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-1018650033533004064760870950178665593375000000000)
      constant := (26640562344104194973714992952218731791901749176271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell134.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3841519876556543053/781250000000000000)
  centralHi := (98342908839847502157/20000000000000000000)
  directionLo := (247121328103191473087/50000000000000000000)
  directionHi := (19769706248255317847/4000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree099.table
  base := (10440167885451450730521159396862456334287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-4111790000702479181120000958432184386000000000000)
      constant := (108560075422230968230033398828477262186138245399343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree099.table
  base := (5220083917518025119256430136119782672551/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-2058075436219953660113688354455369849250000000000)
      constant := (54393849708661780199928066126492803027070282386439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 99 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 99 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247121328103191473087/50000000000000000000)
  centralHi := (19769706248255317847/4000000000000000000)
  directionLo := (99351580450603360173/20000000000000000000)
  directionHi := (248378951126508400433/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree100.table
  base := (5490822138127492620536176851064822618093/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-2076648344900450635600899581038986636750000000000)
      constant := (55402046896100409197018949014804244966244352734477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree100.table
  base := (2745411058345064692117908160254753767773/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-1039425402686949595352817404276704255875000000000)
      constant := (27759084498505347165302107623054048484768516047997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 100 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 100 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99351580450603360173/20000000000000000000)
  centralHi := (248378951126508400433/50000000000000000000)
  directionLo := (499260476793121229559/100000000000000000000)
  directionHi := (12481511919828030739/2500000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree101.table
  base := (461335397720588815053169341916308696201/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-4194803378899323361283597365723762161000000000000)
      constant := (113071254277166081143795232317736533379766332532225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree101.table
  base := (23066769813112876319826400568419601180731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-8398504698111378885190325050605788697000000000000)
      constant := (226616330210085971681505833255762753033246015506459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 101 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 101 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499260476793121229559/100000000000000000000)
  centralHi := (12481511919828030739/2500000000000000000)
  directionLo := (501750569431238103939/100000000000000000000)
  directionHi := (25087528471561905197/5000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree102.table
  base := (3023847468926705799552151900493928677987/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-1059077516999436362841348892342387762125000000000)
      constant := (28840389218968295263561837286341152567321499768643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree102.table
  base := (12095389844707758591282348867509510744903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-4240803087363580503779055433498971673500000000000)
      constant := (115603180749155661837845934370047819075897578534567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 102 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 102 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (501750569431238103939/100000000000000000000)
  centralHi := (25087528471561905197/5000000000000000000)
  directionLo := (504228365090113347399/100000000000000000000)
  directionHi := (2521141825450566737/500000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree103.table
  base := (2533531813182122592790896544079590588823/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-4277816757096167541447193773015339936000000000000)
      constant := (117675001587269032094673043558224620484524567457235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree103.table
  base := (25335318079111671889290319906993949250907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-8564707651342943129925896683390097997000000000000)
      constant := (235842769850648252329905904286327903010410362206523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 103 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 103 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504228365090113347399/100000000000000000000)
  centralHi := (2521141825450566737/500000000000000000)
  directionLo := (253347022085481391629/50000000000000000000)
  directionHi := (506694044170962783259/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree104.table
  base := (3312548126638653900625954767542703323193/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-1079830861548647407882247994165282205875000000000)
      constant := (30002897102617319832817105527003621530527118428377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree104.table
  base := (26500384968300848572416063729718267933723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-8647809127958725252293682499782252647000000000000)
      constant := (240525555265358369234338828579990919689756484247547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 104 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 104 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253347022085481391629/50000000000000000000)
  centralHi := (506694044170962783259/100000000000000000000)
  directionLo := (254573891353376285057/50000000000000000000)
  directionHi := (101829556541350514023/20000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree105.table
  base := (2768598038340553846010047520286111532881/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-4360830135293011721610790180306917711000000000000)
      constant := (122371317344731561898172281655817942576433022789045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree105.table
  base := (3460747543164681644000144913899833559587/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-1091363825571813421832683539521800912125000000000)
      constant := (30656839717622847644308977973515677470897001271043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 105 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 105 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254573891353376285057/50000000000000000000)
  centralHi := (101829556541350514023/20000000000000000000)
  directionLo := (51158975250886278763/10000000000000000000)
  directionHi := (511589752508862787631/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree106.table
  base := (14446052116374435275545737335481714567447/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (3917848)
      previous := (1958924)
      next := (1958924)
      square := (14029257657287400063370052997525000000000000)
      linear := (-1567225640580788113810106224262266500000000000)
      constant := (44412313417384479772444168389023792914257307887) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree106.table
  base := (14446052100188055722556556385807800883223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (3917848)
      previous := (1958924)
      next := (1958924)
      square := (14029257657287400063370052997525000000000000)
      linear := (-1568887874900371928983491301631641500000000000)
      constant := (44505207774349899287168664952763535603121971183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 106 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 106 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51158975250886278763/10000000000000000000)
  centralHi := (511589752508862787631/100000000000000000000)
  directionLo := (257010060653739986199/50000000000000000000)
  directionHi := (514020121307479972399/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree107.table
  base := (1204750262111429800490407061661547354331/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-8887687026979711803548773175196990972000000000000)
      constant := (254320403088102527109743707564894462040423419921475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree107.table
  base := (30118756525273139230009622057146087768607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-8897113557806071619397039948958716597000000000000)
      constant := (254852173870277279800175581344956537063691141661823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 107 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 107 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257010060653739986199/50000000000000000000)
  centralHi := (514020121307479972399/100000000000000000000)
  directionLo := (25821952644302162347/5000000000000000000)
  directionHi := (516439052886043246941/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree108.table
  base := (31365937336515351020553198790818254388131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-8970700405176555983712369582488568747000000000000)
      constant := (259178713616297165216684946602097975386651670525059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree108.table
  base := (15682968656567638434253452683546995650963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-4490107517210926870882412882675435623500000000000)
      constant := (129860233761030925815471150034517921696594655137907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 108 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 108 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25821952644302162347/5000000000000000000)
  centralHi := (516439052886043246941/100000000000000000000)
  directionLo := (259423353605024503953/50000000000000000000)
  directionHi := (518846707210049007907/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree109.table
  base := (16316823289037390052585095345428437850859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-4526856891686700081937982994890073261000000000000)
      constant := (132041654181358354672501495919044297883634184751051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree109.table
  base := (6526729311641642071787940710003142642631/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-9063316511037635864132611581743025897000000000000)
      constant := (264635138230931818119019913418331351884407712377795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 109 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 109 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259423353605024503953/50000000000000000000)
  centralHi := (518846707210049007907/100000000000000000000)
  directionLo := (521243240550500825949/100000000000000000000)
  directionHi := (10424864811010016519/2000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree110.table
  base := (33921884272558232482315785630935907873577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-9136727161570244344039562397071724297000000000000)
      constant := (269034187326747642680600084243962188150420616222153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree110.table
  base := (33921884255678583665737784515094009837319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-9146417987653417986500397398135180547000000000000)
      constant := (269596185996285223418224942343954056452216087269991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 110 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 110 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521243240550500825949/100000000000000000000)
  centralHi := (10424864811010016519/2000000000000000000)
  directionLo := (65453600700284269197/12500000000000000000)
  directionHi := (523628805602274153577/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree111.table
  base := (35230650415864828794153790594134488830837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-9219740539767088524203158804363302072000000000000)
      constant := (274031350507877111346534581375317261171835682662293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree111.table
  base := (35230650401524203015112214764413960857929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-9229519464269200108868183214527335197000000000000)
      constant := (274603610817619054030548361228799734596358602338281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 111 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 111 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65453600700284269197/12500000000000000000)
  centralHi := (523628805602274153577/100000000000000000000)
  directionLo := (526003551597649541403/100000000000000000000)
  directionHi := (131500887899412385351/25000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree112.table
  base := (7311989000914101132466108737612882489617/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-9302753917963932704366755211654879847000000000000)
      constant := (279074797905676903726405960614612972783842749128565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree112.table
  base := (731198899847759443235034477451302211759/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-4656310470442491115617984515459744923500000000000)
      constant := (139828706347256736607513861973762871056678758278775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 112 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 112 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526003551597649541403/100000000000000000000)
  centralHi := (131500887899412385351/25000000000000000000)
  directionLo := (528367624415253239159/100000000000000000000)
  directionHi := (13209190610381330979/2500000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree113.table
  base := (37909768035820187999237053060368067167017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-9385767296160776884530351618946457622000000000000)
      constant := (284164529519789965588701211208988316639699823674313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree113.table
  base := (18954884012735901668931624941746050996827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-4697861208750382176801877423655822248500000000000)
      constant := (142378795813309276772622839757081227798431125241403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 113 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 113 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528367624415253239159/100000000000000000000)
  centralHi := (13209190610381330979/2500000000000000000)
  directionLo := (132680291671157556063/25000000000000000000)
  directionHi := (530721166684630224253/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree114.table
  base := (7856023901447406528921550437354585708791/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-9468780674357621064693948026238035397000000000000)
      constant := (289300545349919050142364376304622264735740526338995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree114.table
  base := (19640059749223671335170461835860398045217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-4739411947058273237985770331851899573500000000000)
      constant := (144952073806821556137810218546488601171371436914113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 114 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 114 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132680291671157556063/25000000000000000000)
  centralHi := (530721166684630224253/100000000000000000000)
  directionLo := (66633039735832722917/12500000000000000000)
  directionHi := (533064317886661783337/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree115.table
  base := (4067099941684604445265983032225345800671/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-4775897026277232622428772216764806586000000000000)
      constant := (147241422697908582751843188542379106963088555585595) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree115.table
  base := (40670999409380848952876390076315182170627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-9561925370732328598339326480095953797000000000000)
      constant := (295097080655345316719032830211112812090200523429603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 115 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 115 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66633039735832722917/12500000000000000000)
  centralHi := (533064317886661783337/100000000000000000000)
  directionLo := (535397214450027703067/100000000000000000000)
  directionHi := (133849303612506925767/25000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree116.table
  base := (42082407763009792467916592213111455044109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-9634807430751309425021140840821190947000000000000)
      constant := (299711429657279535394102516289559941894862744000301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree116.table
  base := (10520601939167496413138963096173152902159/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-2411256711837027680176778074122027111750000000000)
      constant := (75084097687881194871867656942660954732962871536751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 116 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 116 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535397214450027703067/100000000000000000000)
  centralHi := (133849303612506925767/25000000000000000000)
  directionLo := (67214998730487730297/12500000000000000000)
  directionHi := (537719989843901842377/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree117.table
  base := (43514344544374312944451678881691652212099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-9717820808948153605184737248112768722000000000000)
      constant := (304986298134136833799422717633651318477085820557411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree117.table
  base := (2719646533686915026783813924143975104249/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-1216016040495486605384362264110032887125000000000)
      constant := (38202759737751988471026249958293496968432203337522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 117 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 117 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67214998730487730297/12500000000000000000)
  centralHi := (537719989843901842377/100000000000000000000)
  directionLo := (540032774667059302853/100000000000000000000)
  directionHi := (270016387333529651427/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree118.table
  base := (1124170243995589708329123597327860724001/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-1225104273393124723168541706925543312125000000000)
      constant := (38788431353281186516905185549257640818783675477445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree118.table
  base := (44966809755252184777914420310696551213073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-9811229800579674965442683929272417747000000000000)
      constant := (310954142106682308117987250718893381199769239499697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 118 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 118 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540032774667059302853/100000000000000000000)
  centralHi := (270016387333529651427/50000000000000000000)
  directionLo := (271167848366781766661/50000000000000000000)
  directionHi := (542335696733563533323/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree119.table
  base := (23219901704220622975820167007964277317929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-4941923782670920982755965031347962136000000000000)
      constant := (157837443866751454651081152834133638240321991278281) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree119.table
  base := (1857592136182393502737751980305940086043/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-9894331277195457087810469745664572397000000000000)
      constant := (316332583365412079665638574882952577213628840300675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 119 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 119 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271167848366781766661/50000000000000000000)
  centralHi := (542335696733563533323/100000000000000000000)
  directionLo := (108925776231038490179/20000000000000000000)
  directionHi := (34039305072199528181/6250000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree120.table
  base := (74895821077309897517216480054691269189/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-1245857617942335768209440808748437755875000000000)
      constant := (40136076106975427727776074606670092247953022753680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree120.table
  base := (23966662743091503817450085473278840804249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-4988716376905619605089127781028363523500000000000)
      constant := (160878700839056927526686260086174052555491728968761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 120 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 120 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108925776231038490179/20000000000000000000)
  centralHi := (34039305072199528181/6250000000000000000)
  directionLo := (273456225210376994529/50000000000000000000)
  directionHi := (546912450420753989059/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree121.table
  base := (12361844000581554090254617531622474980259/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-2512468580433882581459780719319769955500000000000)
      constant := (81637153548268728454841971974551069282915225627651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree121.table
  base := (12361843999882167147205248005925274700417/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-2515133557606755333136510344612220424250000000000)
      constant := (81807149261178367676021111378354409541718778106913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 121 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 121 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273456225210376994529/50000000000000000000)
  centralHi := (546912450420753989059/100000000000000000000)
  directionLo := (109837304894486670503/20000000000000000000)
  directionHi := (137296631118108338129/25000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree122.table
  base := (50981954946493768080157099431895933817229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-10132887699932374506002719284570657597000000000000)
      constant := (332054903745255965611995736093105163843360478135981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree122.table
  base := (5098195494411896881137196961101028088563/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-5071817853521401727456913597420518173500000000000)
      constant := (166373084732575583369252555715944360805151677621535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 122 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 122 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109837304894486670503/20000000000000000000)
  centralHi := (137296631118108338129/25000000000000000000)
  directionLo := (275725610389653315307/50000000000000000000)
  directionHi := (110290244155861326123/20000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree123.table
  base := (3283566395099262774374491345780571068131/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-1276987634766152335770789461482779421500000000000)
      constant := (42200934689037181960798667420682496412239169090118) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree123.table
  base := (52537062319572405718556089083458346987991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-10226737183658585577281613011233190997000000000000)
      constant := (338310118939379232638427671701229967108102843596599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 123 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 123 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275725610389653315307/50000000000000000000)
  centralHi := (110290244155861326123/20000000000000000000)
  directionLo := (138426663602037065341/25000000000000000000)
  directionHi := (110741330881629652273/20000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree124.table
  base := (54112698127298955104379079089340963599309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-10298914456326062866329912099153813147000000000000)
      constant := (343206335494160544293770934546681415707497184293101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree124.table
  base := (54112698125587999556346917302203926565927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-10309838660274367699649398827625345647000000000000)
      constant := (343920445467360028029614234900605206808128355431303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 124 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 124 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138426663602037065341/25000000000000000000)
  centralHi := (110741330881629652273/20000000000000000000)
  directionLo := (277976469045826556927/50000000000000000000)
  directionHi := (111190587618330622771/20000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree125.table
  base := (55708862363384109932263247256027601442509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-10381927834522907046493508506445390922000000000000)
      constant := (348851477690814978256757278930038711678170838417901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree125.table
  base := (435225487202593682470985686904777741813/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-1299117517111268727752148080502187537125000000000)
      constant := (43697143631133039891865030077761090311795323416912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 125 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 125 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277976469045826556927/50000000000000000000)
  centralHi := (111190587618330622771/20000000000000000000)
  directionLo := (558190182294187638711/100000000000000000000)
  directionHi := (69773772786773454839/12500000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree126.table
  base := (57325555029659025125500797777716245403061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-10464941212719751226657104913736968697000000000000)
      constant := (354542904102237666122558493170945846809105407695829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree126.table
  base := (28662777514213332458193931915892198067971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-5238020806752965972192485230204827473500000000000)
      constant := (177640114842234940428469150891162863942967240526819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 126 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 126 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558190182294187638711/100000000000000000000)
  centralHi := (69773772786773454839/12500000000000000000)
  directionLo := (22416739811007143853/4000000000000000000)
  directionHi := (280209247637589298163/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree127.table
  base := (11792555225197349893345928143137266087237/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-10547954590916595406820701321028546472000000000000)
      constant := (360280614728411480841913346373694385922009443209465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree127.table
  base := (29481388062470478002152856649084870529053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-5279571545060857033376378138400904798500000000000)
      constant := (180514843686780161184872506933386764335494527833917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 127 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 127 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22416739811007143853/4000000000000000000)
  centralHi := (280209247637589298163/50000000000000000000)
  directionLo := (562637983150242285623/100000000000000000000)
  directionHi := (70329747893780285703/12500000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree128.table
  base := (30310262826134990666735930782248501957641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-5315483984556719793492148864160062123500000000000)
      constant := (183032304784662126961817939818224104133838083105449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree128.table
  base := (2424821026055302611694366066341417709383/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-10642244566737496189120542093193964247000000000000)
      constant := (366825522116324100766585601903266784572774712132175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 128 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 128 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562637983150242285623/100000000000000000000)
  centralHi := (70329747893780285703/12500000000000000000)
  directionLo := (112969749990030387697/20000000000000000000)
  directionHi := (282424374975075969243/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree129.table
  base := (62298803608444314159303543347274030627241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-10713981347310283767147894135611702022000000000000)
      constant := (371894888624967930715440873344700997173088108939849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree129.table
  base := (31149401803845668206043669657717280880449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-5362673021676639155744163954793059448500000000000)
      constant := (186333866956376846461380128787618907822378422030561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 129 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 129 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112969749990030387697/20000000000000000000)
  centralHi := (282424374975075969243/50000000000000000000)
  directionLo := (35440681104858499671/6250000000000000000)
  directionHi := (567050897677735994737/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree130.table
  base := (12799521998894513198622615110951993030627/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-10796994725507127947311490542903279797000000000000)
      constant := (377771451895337861261522286506197986744708869848015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree130.table
  base := (15999402498458424573430823782186051063467/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-2702111879992265108464028431494568386750000000000)
      constant := (94639080690711225114359684718057553845175089588363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 130 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35440681104858499671/6250000000000000000)
  centralHi := (567050897677735994737/100000000000000000000)
  directionLo := (569244526362795309721/100000000000000000000)
  directionHi := (284622263181397654861/50000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree131.table
  base := (1314338896206800423432566823171314712003/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-5440004051851986063737543475097428786000000000000)
      constant := (191847149690216102614275506048710320579219433661675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree131.table
  base := (32858472404899001378262293952790465624677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-5445774498292421278111949771185214098500000000000)
      constant := (192245644333298133327544808854322160233594171410053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 131 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (569244526362795309721/100000000000000000000)
  centralHi := (284622263181397654861/50000000000000000000)
  directionLo := (571429734115122952081/100000000000000000000)
  directionHi := (285714867057561476041/50000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree132.table
  base := (6745680805605043932707213856097108834931/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-5481510740950408153819341678743217673500000000000)
      constant := (194831715540125716397105830610354040965869281051295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree132.table
  base := (13491361611118123016954999879709506808353/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-10974650473200624678591685358762582847000000000000)
      constant := (390472631624008587554912763561448160403473235558085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 132 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (571429734115122952081/100000000000000000000)
  centralHi := (285714867057561476041/50000000000000000000)
  directionLo := (35850413573481631629/6250000000000000000)
  directionHi := (114721323435141221213/20000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree133.table
  base := (69217199731622709858092890830536626184091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-11046034860097660487802279764778013122000000000000)
      constant := (395678846994797906257046722955670310014241440389499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree133.table
  base := (69217199731232637857437399929060155230821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-11057751949816406800959471175154737497000000000000)
      constant := (396500351635084502234649855143011303739427151310469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 133 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35850413573481631629/6250000000000000000)
  centralHi := (114721323435141221213/20000000000000000000)
  directionLo := (575775269966185684407/100000000000000000000)
  directionHi := (71971908745773210551/12500000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree134.table
  base := (70998119837088049277575160628432276685063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-11129048238294504667965876172069590897000000000000)
      constant := (401740547124075529538205902624701716691340592712807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree134.table
  base := (70998119836757167266943945286665142825937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-11140853426432188923327256991546892147000000000000)
      constant := (402574448699828149687214303523542808298923697166193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 134 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (575775269966185684407/100000000000000000000)
  centralHi := (71971908745773210551/12500000000000000000)
  directionLo := (577935785136645569559/100000000000000000000)
  directionHi := (14448394628416139239/2500000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree135.table
  base := (72799568372487655087745371346846861154479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-11212061616491348848129472579361168672000000000000)
      constant := (407848531468089454776265713099527082546608093801231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree135.table
  base := (36399784186103498564260244690078121034557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-5611977451523985522847521403969523398500000000000)
      constant := (204347461409122440842635307206232536234161849761373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 135 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (577935785136645569559/100000000000000000000)
  centralHi := (14448394628416139239/2500000000000000000)
  directionLo := (580088253611799918729/100000000000000000000)
  directionHi := (58008825361179991873/10000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree136.table
  base := (18655386334467685875731262700556638411827/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-2823768748672048257073267246663186611750000000000)
      constant := (103500700006711459231459929782642612975840856176403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree136.table
  base := (74621545337632699220599859311121432823693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-11307056379663753168062828624331201447000000000000)
      constant := (414861773990341022709587418387928040097878873672877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 136 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (580088253611799918729/100000000000000000000)
  centralHi := (58008825361179991873/10000000000000000000)
  directionLo := (291116382317821839579/50000000000000000000)
  directionHi := (582232764635643679159/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree137.table
  base := (19116012683323227462248490717822655192363/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-2844522093221259302114166348486081055500000000000)
      constant := (105050838200087907177493308115923748809948863482507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree137.table
  base := (4779003170818188744313456310150452479359/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-1423769732034941911303826805090419512125000000000)
      constant := (52634375277015458678959803529906481427124839175102) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 137 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291116382317821839579/50000000000000000000)
  centralHi := (582232764635643679159/100000000000000000000)
  directionLo := (146092351453657087983/25000000000000000000)
  directionHi := (584369405814628351933/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree138.table
  base := (78327084558814760157658667665066996179061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-11461101751081881388620261801235901997000000000000)
      constant := (426450189788614409488021793304333649203918321159829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree138.table
  base := (9790885569830442816160421873300984819347/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-1434157416611914676599800032139438843375000000000)
      constant := (53416825936950065429001782574082804212329293133683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 138 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146092351453657087983/25000000000000000000)
  centralHi := (584369405814628351933/100000000000000000000)
  directionLo := (4582017680932985191/781250000000000000)
  directionHi := (586498263159422104449/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree139.table
  base := (40105323407250385315279435098631944908281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-5772057564639362784391929104263739886000000000000)
      constant := (216371655495821121310407562061805750262993273728409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree139.table
  base := (80210646814355573015658878405876235296783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-11556360809511099535166186073507665397000000000000)
      constant := (433640589828779751837361487959623984216459445323887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 139 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4582017680932985191/781250000000000000)
  centralHi := (586498263159422104449/100000000000000000000)
  directionLo := (294309710562655276419/50000000000000000000)
  directionHi := (588619421125310552839/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree140.table
  base := (2566085546888073078600720312528942868829/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-1453391063434446218618431826977382193375000000000)
      constant := (54885339551180444596711142885609762409668795073524) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree140.table
  base := (8211473750029521301123806732215754436191/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-5819731143063440828766985944949910023500000000000)
      constant := (219996474607834935702202894252991935102697647831995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 140 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294309710562655276419/50000000000000000000)
  centralHi := (588619421125310552839/100000000000000000000)
  directionLo := (295366481325645953257/50000000000000000000)
  directionHi := (118146592530258381303/20000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree141.table
  base := (21009839154159248428945792215928908804027/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-2927535471418103482277762755777658830500000000000)
      constant := (111367101510506761830231203079466488951327967762203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree141.table
  base := (84039356616532590370944260863570586566583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-11722563762742663779901757706291974697000000000000)
      constant := (446391685656279652286848538656113563823447134456087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 141 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295366481325645953257/50000000000000000000)
  centralHi := (118146592530258381303/20000000000000000000)
  directionLo := (592838969197917678491/100000000000000000000)
  directionHi := (148209742299479419623/25000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree142.table
  base := (85984504163227745327836431415864778423731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-11793155263869258109274647430402213097000000000000)
      constant := (451900379889401594623731870383460380306770024333459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree142.table
  base := (2687015755098100679616897523436361915081/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-1475708154919805737783692940335516168375000000000)
      constant := (56604599893827254790095539282058818067851365014436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 142 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (592838969197917678491/100000000000000000000)
  centralHi := (148209742299479419623/25000000000000000000)
  directionLo := (59493752078392780873/10000000000000000000)
  directionHi := (594937520783927808731/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree143.table
  base := (4397509007013127069171752465911380929177/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-2969042160516525572359560959423447718000000000000)
      constant := (114594659487894049116558330623321904367779854052765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree143.table
  base := (43975090070093742987068223945756553313283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-5944383357987114012318664669538141998500000000000)
      constant := (229664144849347040582980553774391015061260428892387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 143 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59493752078392780873/10000000000000000000)
  centralHi := (594937520783927808731/100000000000000000000)
  directionLo := (191049182726952581/32000000000000000)
  directionHi := (298514348010863407813/50000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree144.table
  base := (89936384547813823540587930066109203029647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-11959182020262946469601840244985368647000000000000)
      constant := (464903180228559912365162075376158786417084905670383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree144.table
  base := (11242048068468773791966808354726817787779/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-1496483524073751268375639394433554830875000000000)
      constant := (58233269662564610758046488730009359238135752184931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 144 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191049182726952581/32000000000000000)
  centralHi := (298514348010863407813/50000000000000000000)
  directionLo := (599112572151745475471/100000000000000000000)
  directionHi := (37444535759484092217/6250000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree145.table
  base := (22985779346488540338583890878039597419079/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-3010548849614947662441359163069236605500000000000)
      constant := (117868501680090454457997112516838959652964488590631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree145.table
  base := (18388623477180042936405691010779912771899/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-12054969669205792269372900971860593297000000000000)
      constant := (472450401956095567332732797342856752603591312498055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 145 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (599112572151745475471/100000000000000000000)
  centralHi := (37444535759484092217/6250000000000000000)
  directionLo := (75148653134466315559/12500000000000000000)
  directionHi := (601189225075730524473/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree146.table
  base := (93970378654755953209683262775668336994493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-12125208776656634829929033059568524197000000000000)
      constant := (478091117426990966971745636287862572495011090394077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree146.table
  base := (93970378654710220716743759842880055317501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-12138071145821574391740686788252747947000000000000)
      constant := (479081023665439212006581531387202366543298407816989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 146 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75148653134466315559/12500000000000000000)
  centralHi := (601189225075730524473/100000000000000000000)
  directionLo := (301629364694501488061/50000000000000000000)
  directionHi := (603258729389002976123/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree147.table
  base := (19203633670858236610617367976545300228879/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-12208222154853479010092629466860101972000000000000)
      constant := (484754512348456362059993601250741540003250953914155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree147.table
  base := (1200227104428155197839743332557614584513/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-1527646577804669564263559075580612824625000000000)
      constant := (60719752803569606288109470085423088918606430938570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 147 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301629364694501488061/50000000000000000000)
  centralHi := (603258729389002976123/100000000000000000000)
  directionLo := (605321158411723842557/100000000000000000000)
  directionHi := (302660579205861921279/50000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree148.table
  base := (24521621621157805947484462369388728375593/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-3072808883262580797564056468537919936750000000000)
      constant := (122866047871191732238952264531178681295761460651977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree148.table
  base := (9808648648459836250937427522232114718737/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-6152137049526569318238129210518528623500000000000)
      constant := (246240699122728715898400824781512710933573139726965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 148 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (605321158411723842557/100000000000000000000)
  centralHi := (302660579205861921279/50000000000000000000)
  directionLo := (303688292109602168103/50000000000000000000)
  directionHi := (607376584219204336207/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree149.table
  base := (1565239578841354369876348205429902681027/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-1546781113905895921302477785180407190250000000000)
      constant := (62277519354491437173856199301558833899356107921624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree149.table
  base := (20035066609163765174822345841404468113929/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-12387375575668920758844044237429211897000000000000)
      constant := (499251151116149806330952816367220217351223772611405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 149 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303688292109602168103/50000000000000000000)
  centralHi := (607376584219204336207/100000000000000000000)
  directionLo := (152356269417824000591/25000000000000000000)
  directionHi := (121885015534259200473/20000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree150.table
  base := (6392794252375453826576401638079264462857/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-1557157786180501443822927336091854412125000000000)
      constant := (63127800300244848165979494727202348954191511800146) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree150.table
  base := (102284708037983652920412174570902254875549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-12470477052284702881211830053821366547000000000000)
      constant := (506067281040642708937334929068856705438683916534461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 150 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152356269417824000591/25000000000000000000)
  centralHi := (121885015534259200473/20000000000000000000)
  directionLo := (611466708440894689343/100000000000000000000)
  directionHi := (9554167319388979521/1562500000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree151.table
  base := (52207305730590843648709730622525432497331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-6270137833820427865373507548013206536000000000000)
      constant := (255935467091428693355396424969426863218307708723859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree151.table
  base := (104414611461161678274099982676495219391691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-12553578528900485003579615870213521197000000000000)
      constant := (512929788018944748039079089754279663095067767305899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 151 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (611466708440894689343/100000000000000000000)
  centralHi := (9554167319388979521/1562500000000000000)
  directionLo := (12270030900831815919/2000000000000000000)
  directionHi := (613501545041590795951/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree152.table
  base := (53282521657718804839024083117751646065373/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-6311644522918849955455305751658995423500000000000)
      constant := (259382875089317881018964457825923995232844407974397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree152.table
  base := (13320630414427581492434980444701745616243/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-1579585000689533390743425210825709480875000000000)
      constant := (64979834006383049552137923844927637894675339679827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 152 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12270030900831815919/2000000000000000000)
  centralHi := (613501545041590795951/100000000000000000000)
  directionLo := (307764827427248420933/50000000000000000000)
  directionHi := (615529654854496841867/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree153.table
  base := (849500028131574659894453662757772620673/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-1588287803004318011384275988826196077750000000000)
      constant := (65713356298662778909919618752605783543997274457552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree153.table
  base := (108736003600827185327522346767290577299019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-12719781482132049248315187502997830497000000000000)
      constant := (526793933137009984460425383007811956677530316341291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 153 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307764827427248420933/50000000000000000000)
  centralHi := (615529654854496841867/100000000000000000000)
  directionLo := (12351022083085641621/2000000000000000000)
  directionHi := (617551104154282081051/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree154.table
  base := (110927492317458890984381817110497032152827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-12789315802231388271237804317901146397000000000000)
      constant := (532694234814864968738680174897527192740049114525403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree154.table
  base := (22185498463489342485128341038522068698763/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-12802882958747831370682973319389985147000000000000)
      constant := (533795571276789695310074320394448324346450978560535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 154 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12351022083085641621/2000000000000000000)
  centralHi := (617551104154282081051/100000000000000000000)
  directionLo := (619565958134442617637/100000000000000000000)
  directionHi := (309782979067221308819/50000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree155.table
  base := (11313950946535378354186271758214702560139/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-6436164590214116225700700362596362086000000000000)
      constant := (269863951727665999761046791736681574281977375544855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree155.table
  base := (113139509465343463480156740072068114156013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-12885984435363613493050759135782139797000000000000)
      constant := (540843586470411561567833178834498719314544652057357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 155 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (619565958134442617637/100000000000000000000)
  centralHi := (309782979067221308819/50000000000000000000)
  directionLo := (310787140465917142257/50000000000000000000)
  directionHi := (124314856186366856903/20000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree156.table
  base := (115372055044589193802911813397901959992697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-12955342558625076631564997132484301947000000000000)
      constant := (546807856310711197333002006591396719145785130551833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree156.table
  base := (4614882201783217959520776031789416695151/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-12969085911979395615418544952174294447000000000000)
      constant := (547937978717883463294252405176114289069591320945975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 156 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310787140465917142257/50000000000000000000)
  centralHi := (124314856186366856903/20000000000000000000)
  directionLo := (311788067825247201697/50000000000000000000)
  directionHi := (124715227130098880679/20000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree157.table
  base := (23525025811045372372070263976290405407701/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-13038355936821920811728593539775879722000000000000)
      constant := (553934093381010283355864603067856569455324618623945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree157.table
  base := (117625129055219452152133245524635148986877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-13052187388595177737786330768566449097000000000000)
      constant := (555078748019213127065115901719569515147737705325853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 157 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311788067825247201697/50000000000000000000)
  centralHi := (124715227130098880679/20000000000000000000)
  directionLo := (125114316876955491717/20000000000000000000)
  directionHi := (312785792192388729293/50000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree158.table
  base := (119898731497327306438405011034109152254309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-13121369315018764991892189947067457497000000000000)
      constant := (561106614666236826031407730000998254227147081588101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree158.table
  base := (119898731497321028255307870425038563008831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-13135288865210959860154116584958603747000000000000)
      constant := (562265894374408125893148087045339461146178707347359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 158 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125114316876955491717/20000000000000000000)
  centralHi := (312785792192388729293/50000000000000000000)
  directionLo := (627560688241828681927/100000000000000000000)
  directionHi := (78445086030228585241/12500000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree159.table
  base := (15274107796368728612380983873091943847769/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55651250000000000000000000000000000000000000
      center := (979462)
      previous := (489731)
      next := (489731)
      square := (3507314414321850015842513249381250000000000)
      linear := (-587592679477376698649687894017401000000000000)
      constant := (25290380035884578211002891729118920978921523649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree159.table
  base := (30548215592736127415161136842669304112309/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 111302500000000000000000000000000000000000000
      center := (1958924)
      previous := (979462)
      next := (979462)
      square := (7014628828643700031685026498762500000000000)
      linear := (-1176432034694441258679414596061833250000000000)
      constant := (50685245441747586316603735196629416838384108989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 159 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (627560688241828681927/100000000000000000000)
  centralHi := (78445086030228585241/12500000000000000000)
  directionLo := (12590870147268371213/2000000000000000000)
  directionHi := (629543507363418560651/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree160.table
  base := (124507521676152521945524464901836743143339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-13287396071412453352219382761650613047000000000000)
      constant := (575590509881501794978394755837143482778930229093771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree160.table
  base := (62253760838074007679266248827324817838639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-6650745909221262052444844108871456523500000000000)
      constant := (288389659123211828638494809258779167715918277795471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 160 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12590870147268371213/2000000000000000000)
  centralHi := (629543507363418560651/100000000000000000000)
  directionLo := (631520100947160340593/100000000000000000000)
  directionHi := (315760050473580170297/50000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree161.table
  base := (126842709412992282098878621262370748918807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-13370409449609297532382979168942190822000000000000)
      constant := (582901883811554601743468667638079544052208305909623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree161.table
  base := (126842709412988464158858728240351494524577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-13384593295058306227257474034135067697000000000000)
      constant := (584105595763258576401317193828611789327629897561153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 161 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (631520100947160340593/100000000000000000000)
  centralHi := (315760050473580170297/50000000000000000000)
  directionLo := (316745263633565850961/50000000000000000000)
  directionHi := (633490527267131701923/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree162.table
  base := (129198425581524825176623805480477234862003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-13453422827806141712546575576233768597000000000000)
      constant := (590259541956563629644546169574880056156975080696467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree162.table
  base := (129198425581521590776887553704058120410823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-13467694771674088349625259850527222347000000000000)
      constant := (591478250333987607381352810283332733253877994449447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 162 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316745263633565850961/50000000000000000000)
  centralHi := (633490527267131701923/100000000000000000000)
  directionLo := (158863710923480232699/25000000000000000000)
  directionHi := (635454843693920930797/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree163.table
  base := (131574670181804704131419988770769312422723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-13536436206002985892710171983525346372000000000000)
      constant := (597663484316535701046010358838399244143842090368547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree163.table
  base := (13157467018180196418708556299037220869543/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-6775398124144935235996522833459688498500000000000)
      constant := (299448640979308787292579256771353114800125916217635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 163 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158863710923480232699/25000000000000000000)
  centralHi := (635454843693920930797/100000000000000000000)
  directionLo := (637413106714117096187/100000000000000000000)
  directionHi := (159353276678529274047/25000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree164.table
  base := (16746430401735666089463078616844383070483/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-1702431198024978759109221048852115518375000000000)
      constant := (75639213861434686918026085050719096537189854963187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree164.table
  base := (133971443213883007724772028364605984814683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-13633897724905652594360831483311531647000000000000)
      constant := (606362690637155159107750007448084097705266015676987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 164 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (637413106714117096187/100000000000000000000)
  centralHi := (159353276678529274047/25000000000000000000)
  directionLo := (639365371949262964293/100000000000000000000)
  directionHi := (319682685974631482147/50000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree165.table
  base := (3409718616945474663223297279529907666277/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-1712807870299584281629670599763562740250000000000)
      constant := (76576277710174443949951238607108746446293295762265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree165.table
  base := (68194372338908510252038465190462884212529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-6858499600760717358364308649851843148500000000000)
      constant := (306937238184803450724807770023575157163085044137681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 165 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (639365371949262964293/100000000000000000000)
  centralHi := (319682685974631482147/50000000000000000000)
  directionLo := (128262338834857728319/20000000000000000000)
  directionHi := (160327923543572160399/25000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree166.table
  base := (138826574573656865080165762741008952116813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-13785476340593518433200961205400079697000000000000)
      constant := (620153016686296271295940769303151711098154102088557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree166.table
  base := (138826574573655199794993111866220220444959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-13800100678137216839096403116095840947000000000000)
      constant := (621432639155979204315178611297492890857313925165951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 166 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128262338834857728319/20000000000000000000)
  centralHi := (160327923543572160399/25000000000000000000)
  directionLo := (643252127335443229951/100000000000000000000)
  directionHi := (2512703622404075117/390625000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree167.table
  base := (35321233225362268640643144402554789880681/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19704092379660153389003239435023862500000000000)
      linear := (-3467122429697590653341139403172914368000000000000)
      constant := (156935523976546480297088083691536087575324086832009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree167.table
  base := (70642466450723832032295607163387115643087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39408184759320306778006478870047725000000000000)
      linear := (-6941601077376499480732094466243997798500000000000)
      constant := (314518589498139167747160269476395002991008366602543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 167 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (643252127335443229951/100000000000000000000)
  centralHi := (2512703622404075117/390625000000000000)
  directionLo := (645186724567741101347/100000000000000000000)
  directionHi := (161296681141935275337/25000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree168.table
  base := (8985238728827791943113886346765540225243/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9852046189830076694501619717511931250000000000)
      linear := (-1743937887123400849191019252497904405875000000000)
      constant := (79422182417633829526169060258903748220005668961654) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree168.table
  base := (143763819661243476439640972488589875562383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-13966303631368781083831974748880150247000000000000)
      constant := (636688095890510430796603888258541034164405205602287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 168 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell134.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (645186724567741101347/100000000000000000000)
  centralHi := (161296681141935275337/25000000000000000000)
  directionLo := (129423107642387750889/20000000000000000000)
  directionHi := (323557769105969377223/50000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree169.table
  base := (146263234853091680189180298721512533120671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-14034516475184050973691750427274813022000000000000)
      constant := (643059106990956422406840018249875444439041690597119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree169.table
  base := (146263234853090668391561460946197276845993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78816369518640613556012957740095450000000000000)
      linear := (-14049405107984563206199760565272304897000000000000)
      constant := (644385389838681497013300246788390794853551416277577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 169 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell134.Kernel169
