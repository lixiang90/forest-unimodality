import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell136.Parameters
import ForestUnimodality.BinomialMassData.Q31833_60208.Batch000_049
import ForestUnimodality.BinomialMassData.Q31833_60208.Batch050_099
import ForestUnimodality.BinomialMassData.Q31833_60208.Batch100_149
import ForestUnimodality.BinomialMassData.Q23881_45156.Batch000_049
import ForestUnimodality.BinomialMassData.Q23881_45156.Batch050_099
import ForestUnimodality.BinomialMassData.Q23881_45156.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree000.table
  base := (561897318774466302715353547/10000000000000000000000000)
  polynomial :=
    { denominator := 602080000000000000000000000000000000000000000
      center := (3851793)
      previous := (0)
      next := (3433375)
      square := (89346684858932428263678103372800000000000000)
      linear := (-413695567168021093493734951310400000000000000)
      constant := (33830713768773067153886006357776000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree000.table
  base := (561897318774466302715353547/10000000000000000000000000)
  polynomial :=
    { denominator := 451560000000000000000000000000000000000000000
      center := (2889601)
      previous := (0)
      next := (2574275)
      square := (67010013644199321197758577529600000000000000)
      linear := (-310271675376015820120301213482800000000000000)
      constant := (25373035326579800365414504768332000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree001.table
  base := (337642787091314129462784838829207160969637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-1912258046642562873431632754864328000000000000000)
      constant := (77414321200757927248197898413849500165444220618448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree001.table
  base := (168792162272053993913656937348273801496423/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-1434263337079468196033305564666506000000000000000)
      constant := (58051005336210244876596175604681576999083261811688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (311979165212320689/625000000000000000)
  directionHi := (49916666433971310241/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree002.table
  base := (212005817526323895964175043502336569055653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-2267779674031862372046340887947620800000000000000)
      constant := (50054698393801093770623118731074534403331470165712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree002.table
  base := (211940514844346272302846852477265432637713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-1700974359718988860953917662997235600000000000000)
      constant := (37530398272433944493143234694648603208097582241964) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311979165212320689/625000000000000000)
  centralHi := (49916666433971310241/100000000000000000000)
  directionLo := (1764820666484401639/2500000000000000000)
  directionHi := (70592826659376065561/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree003.table
  base := (5601058224825921806809551004719867412947/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-2623301301421161870661049021030913600000000000000)
      constant := (35039858637109192018468344578483446289968923217200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree003.table
  base := (139970616712300852313331085075712592750217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-1967685382358509525874529761327965200000000000000)
      constant := (26271222710324697676880446785271157205254970080076) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1764820666484401639/2500000000000000000)
  centralHi := (70592826659376065561/100000000000000000000)
  directionLo := (86458202408106278219/100000000000000000000)
  directionHi := (4322910120405313911/5000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree004.table
  base := (3898079408962081838025592815822457960557/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-2978822928810461369275757154114206400000000000000)
      constant := (26875040980340616384672427046096884686752981653200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree004.table
  base := (97408287252842479232602066563287292686567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-2234396404998030190795141859658694800000000000000)
      constant := (20150092452998751179133725167543199519931032997876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86458202408106278219/100000000000000000000)
  centralHi := (4322910120405313911/5000000000000000000)
  directionLo := (311979165212320689/312500000000000000)
  directionHi := (99833332867942620481/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree005.table
  base := (14233408631941542976196834195450491985521/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-3334344556199760867890465287197499200000000000000)
      constant := (22588793278211143489196680038977975811849833043920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree005.table
  base := (17783423882841646989880766215547081715441/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-2501107427637550855715753957989424400000000000000)
      constant := (16937659221030961919859891221512095518277814537392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311979165212320689/312500000000000000)
  centralHi := (99833332867942620481/100000000000000000000)
  directionLo := (1744016552445966677/1562500000000000000)
  directionHi := (111617059356541867329/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree006.table
  base := (54053529515962255261699846553780146568773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-3689866183589060366505173420280792000000000000000)
      constant := (20568419567394554602623800055619318028137532842192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree006.table
  base := (54027862556328897719259839524265544429723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-2767818450277071520636366056320154000000000000000)
      constant := (15424251666888730857997699446388542720022635638244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1744016552445966677/1562500000000000000)
  centralHi := (111617059356541867329/100000000000000000000)
  directionLo := (61135181211971042321/50000000000000000000)
  directionHi := (122270362423942084643/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree007.table
  base := (4222763097824526181471587623046623391727/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-4045387810978359865119881553364084800000000000000)
      constant := (19933992601510576106778156026217302136993203498080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree007.table
  base := (42207312315029204809860902665116763386391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-3034529472916592185556978154650883600000000000000)
      constant := (14949981670804685624498445463237492791411706320948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61135181211971042321/50000000000000000000)
  centralHi := (122270362423942084643/100000000000000000000)
  directionLo := (26413417132330687193/20000000000000000000)
  directionHi := (66033542830826717983/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree008.table
  base := (16776664895095029698690031731497567271281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-4400909438367659363734589686447377600000000000000)
      constant := (20201570421884760865850880570152332820806649807648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree008.table
  base := (33536637586021760831191546186122471257853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-3301240495556112850477590252981613200000000000000)
      constant := (15151996507104919559233484198753494172506092685884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26413417132330687193/20000000000000000000)
  centralHi := (66033542830826717983/50000000000000000000)
  directionLo := (1764820666484401639/1250000000000000000)
  directionHi := (141185653318752131121/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree009.table
  base := (42946917360156262329185809547722790421/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-4756431065756958862349297819530670400000000000000)
      constant := (21101814696553952058525890421698507975129411490000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree009.table
  base := (5365518006454734952546915363989369161301/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-3567951518195633515398202351312342800000000000000)
      constant := (15828386608593176317293544564082897791644625192140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1764820666484401639/1250000000000000000)
  centralHi := (141185653318752131121/100000000000000000000)
  directionLo := (149749999301913930721/100000000000000000000)
  directionHi := (74874999650956965361/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree010.table
  base := (21419792802903687807226707271954762643337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-5111952693146258360964005952613963200000000000000)
      constant := (22482176485060577917335295424578901390152618303248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree010.table
  base := (5351816651094175254742014031336465389251/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-3834662540835154180318814449643072400000000000000)
      constant := (16864810924466622608864691340798359997173357284112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149749999301913930721/100000000000000000000)
  centralHi := (74874999650956965361/50000000000000000000)
  directionLo := (39462589783556068601/25000000000000000000)
  directionHi := (31570071826844854881/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree011.table
  base := (16896184187271269688150504040121177098913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-5467474320535557859578714085697256000000000000000)
      constant := (24254057544514247699505473085493954971192604740752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree011.table
  base := (8442448650243410020456553616616728762463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-4101373563474674845239426547973802000000000000000)
      constant := (18194869023530358890813568162142486800087286469928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39462589783556068601/25000000000000000000)
  centralHi := (31570071826844854881/20000000000000000000)
  directionLo := (165554853346810521411/100000000000000000000)
  directionHi := (41388713336702630353/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree012.table
  base := (13035929682504490321225584501079957325803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-5822995947924857358193422218780548800000000000000)
      constant := (26364200273834706771808569225786420051938536651312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree012.table
  base := (407049910279406726251006459432006990517/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-4368084586114195510160038646304531600000000000000)
      constant := (19778648771654242291818237490789561390042413071232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165554853346810521411/100000000000000000000)
  centralHi := (41388713336702630353/25000000000000000000)
  directionLo := (172916404816212556439/100000000000000000000)
  directionHi := (4322910120405313911/2500000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree013.table
  base := (2422836134787680294048755782553296383523/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-6178517575314156856808130351863841600000000000000)
      constant := (28779144816846405094522028983872242611057567704768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree013.table
  base := (9681794047907624734005391005163238234163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-4634795608753716175080650744635261200000000000000)
      constant := (21591074428214135990224593779523292811796115842564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172916404816212556439/100000000000000000000)
  centralHi := (4322910120405313911/2500000000000000000)
  directionLo := (44994275081978939931/25000000000000000000)
  directionHi := (7199084013116630389/4000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree014.table
  base := (6764675607344061821699139390812801292757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-6534039202703456355422838484947134400000000000000)
      constant := (31476743955591207028522236740778673218701721534928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree014.table
  base := (4222376170315357095214427931137862317/6250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-4901506631393236840001262842965990800000000000000)
      constant := (23615546958567294492370546614437849259983070201600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44994275081978939931/25000000000000000000)
  centralHi := (7199084013116630389/4000000000000000000)
  directionLo := (2918297870090618879/1562500000000000000)
  directionHi := (186771063685799608257/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree015.table
  base := (4187508273184866148734769953940374850519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-6889560830092755854037546618030427200000000000000)
      constant := (34441497490150892766710357068147779780907180443376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree015.table
  base := (2089622194306432493620544768548656143479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-5168217654032757504921874941296720400000000000000)
      constant := (25840447737743656765826068007297920037149221310824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2918297870090618879/1562500000000000000)
  centralHi := (186771063685799608257/100000000000000000000)
  directionLo := (193326417796961652673/100000000000000000000)
  directionHi := (96663208898480826337/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree016.table
  base := (477330393471381144484215895101318126483/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-7245082457482055352652254751113720000000000000000)
      constant := (37661959254587618105089141354129981554800809960128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree016.table
  base := (950810914210663473709156421708420862121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-5434928676672278169842487039627450000000000000000)
      constant := (28257195742783218206298288767855767395138217402776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193326417796961652673/100000000000000000000)
  centralHi := (96663208898480826337/50000000000000000000)
  directionLo := (199666665735885240961/100000000000000000000)
  directionHi := (99833332867942620481/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree017.table
  base := (-54486497258910342498249065254792410421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-7600604084871354851266962884197012800000000000000)
      constant := (41129273251748016703510071173471461565072680923232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree017.table
  base := (-116143126039200235543597080298874278911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-5701639699311798834763099137958179600000000000000)
      constant := (30859150876567858735302216624686024936410405248492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199666665735885240961/100000000000000000000)
  centralHi := (99833332867942620481/50000000000000000000)
  directionLo := (8232467527439494239/4000000000000000000)
  directionHi := (25726461023248419497/12500000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree018.table
  base := (-1898762068401712592732065350688637363469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-7956125712260654349881671017280305600000000000000)
      constant := (44836328440425154228444823596337616256857032539824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree018.table
  base := (-23817894085935802900331033805120392983/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-5968350721951319499683711236288909200000000000000)
      constant := (33640980807082928069419093370848626283213733638080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8232467527439494239/4000000000000000000)
  centralHi := (25726461023248419497/12500000000000000000)
  directionLo := (5294461999453204917/2500000000000000000)
  directionHi := (211778479978128196681/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree019.table
  base := (-3485952152591207950177263161833250537027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-8311647339649953848496379150363598400000000000000)
      constant := (48777255372834676763219971926540763361221710758992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree019.table
  base := (-3492147276436160340336217665889455713253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-6235061744590840164604323334619638800000000000000)
      constant := (36598283890707916080756319993637209161387863762916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5294461999453204917/2500000000000000000)
  centralHi := (211778479978128196681/100000000000000000000)
  directionLo := (27197713073013718107/12500000000000000000)
  directionHi := (217581704584109744857/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree020.table
  base := (-2446173560566702200561290922237380626427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-8667168967039253347111087283446891200000000000000)
      constant := (52947114104314798442306313876638004630798970042784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree020.table
  base := (-979618623482784608325599261532513129123/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-6501772767230360829524935432950368400000000000000)
      constant := (39727355361188833997263678087567962905813969892780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27197713073013718107/12500000000000000000)
  centralHi := (217581704584109744857/100000000000000000000)
  directionLo := (1744016552445966677/781250000000000000)
  directionHi := (223234118713083734657/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree021.table
  base := (-1534136177932898019847219949307879817807/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-9022690594428552845725795416530184000000000000000)
      constant := (57341691081123179103288873916237256879882474919488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree021.table
  base := (-3070933143482137706733709862624664071179/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-6768483789869881494445547531281098000000000000000)
      constant := (43025035138272916432983619411451045056413055937976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1744016552445966677/781250000000000000)
  centralHi := (223234118713083734657/100000000000000000000)
  directionLo := (114373451186767464487/50000000000000000000)
  directionHi := (9149876094941397159/4000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree022.table
  base := (-7234551884044160387429481711816883819461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-9378212221817852344340503549613476800000000000000)
      constant := (61957359723196795126862882569393975049009068017456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree022.table
  base := (-3619736714981328423974045823518569103587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-7035194812509402159366159629611827600000000000000)
      constant := (46488603340401452919020511653930508284520709771128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114373451186767464487/50000000000000000000)
  centralHi := (9149876094941397159/4000000000000000000)
  directionLo := (14633119932484264057/6250000000000000000)
  directionHi := (234129918919748224913/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree023.table
  base := (-4100115066398007569237846218737402892383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-9733733849207151842955211682696769600000000000000)
      constant := (66790979532809290115837336432015137269528573032736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree023.table
  base := (-8204775694144247939142815464137240325643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-7301905835148922824286771727942557200000000000000)
      constant := (50115704653240873961883259283143452753543361035996) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14633119932484264057/6250000000000000000)
  centralHi := (234129918919748224913/100000000000000000000)
  directionLo := (119695961211362762387/50000000000000000000)
  directionHi := (9575676896909020991/4000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree024.table
  base := (-9045633414425610022793957519194760516369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-10089255476596451341569919815780062400000000000000)
      constant := (71839819532996069792566691120959174354779003098224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree024.table
  base := (-9049826565207662516859557708185834539509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-7568616857788443489207383826273286800000000000000)
      constant := (53904290924056802102822045775478129194174184595748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119695961211362762387/50000000000000000000)
  centralHi := (9575676896909020991/4000000000000000000)
  directionLo := (61135181211971042321/25000000000000000000)
  directionHi := (48908144969576833857/20000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree025.table
  base := (-2445318694364901223703529994244688215629/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-10444777103985750840184627948863355200000000000000)
      constant := (77101497859055650884343075023318906000920634796736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree025.table
  base := (-9785138473066886973830832676583122512669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-7835327880427964154127995924604016400000000000000)
      constant := (57852575859439044908419357839981300212074827827268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61135181211971042321/25000000000000000000)
  centralHi := (48908144969576833857/20000000000000000000)
  directionLo := (124791666084928275601/50000000000000000000)
  directionHi := (249583332169856551203/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree026.table
  base := (-5208171546356326821527398912463705988011/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-10800298731375050338799336081946648000000000000000)
      constant := (82573932655569558723359595487476583538990472516512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree026.table
  base := (-2604974882876578076312558381871915128041/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-8102038903067484819048608022934746000000000000000)
      constant := (61958998196459863906026961874611739180797574451408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124791666084928275601/50000000000000000000)
  centralHi := (249583332169856551203/100000000000000000000)
  directionLo := (2036208449602573437/800000000000000000)
  directionHi := (127263028100160839813/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree027.table
  base := (-10958883054930750014637540580121941110163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-11155820358764349837414044215029940800000000000000)
      constant := (88255301294743286373101302038172395372352708839248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree027.table
  base := (-5481076781978867331342379825555756094193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-8368749925707005483969220121265475600000000000000)
      constant := (66222191112328854373887997965109848894802732833192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2036208449602573437/800000000000000000)
  centralHi := (127263028100160839813/50000000000000000000)
  directionLo := (259374607224318834659/100000000000000000000)
  directionHi := (12968730361215941733/5000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree028.table
  base := (-11415946944044129749599079801030314786473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-11511341986153649336028752348113233600000000000000)
      constant := (94144005992966474692948031714197703096005494497008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree028.table
  base := (-1427368986673587574899203046148420430111/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-8635460948346526148889832219596205200000000000000)
      constant := (70640956431947287823522234979762194892151252919136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259374607224318834659/100000000000000000000)
  centralHi := (12968730361215941733/5000000000000000000)
  directionLo := (264134171323306871931/100000000000000000000)
  directionHi := (66033542830826717983/25000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree029.table
  base := (-235874478037204957687089563219646473557/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-11866863613542948834643460481196526400000000000000)
      constant := (100238644521535787222491169449953440651343079093600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree029.table
  base := (-11796482646954355418038675574127165198621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-8902171970986046813810444317926934800000000000000)
      constant := (75214242656199440094364744709662612659559296876612) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264134171323306871931/100000000000000000000)
  centralHi := (66033542830826717983/25000000000000000000)
  directionLo := (8400296105302952563/3125000000000000000)
  directionHi := (268809475369694482017/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree030.table
  base := (-6048825416675917950513970255896943390791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-12222385240932248333258168614279819200000000000000)
      constant := (106537985080559210870874727730362274120094924682272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree030.table
  base := (-3025045420547415460625315133890013326783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-9168882993625567478731056416257664400000000000000)
      constant := (79941126113149051239571157812183456626264023696304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8400296105302952563/3125000000000000000)
  centralHi := (268809475369694482017/100000000000000000000)
  directionLo := (273404842013470460887/100000000000000000000)
  directionHi := (34175605251683807611/12500000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree031.table
  base := (-2466501601555448555463371413410358295107/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-12577906868321547831872876747363112000000000000000)
      constant := (113040944639307726019135950134890843415258640553360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree031.table
  base := (-2466965641824544634099957026316228780781/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-9435594016265088143651668514588394000000000000000)
      constant := (84820794709735908009765690581991683881288625280660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273404842013470460887/100000000000000000000)
  centralHi := (34175605251683807611/12500000000000000000)
  directionLo := (138962118241169507353/50000000000000000000)
  directionHi := (277924236482339014707/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree032.table
  base := (-1250250175387472956886318710935668428987/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-12933428495710847330487584880446404800000000000000)
      constant := (119746570200568479334250699912615245906812732991520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree032.table
  base := (-6252313751241993474325688555215450927213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-9702305038904608808572280612919123600000000000000)
      constant := (89852533877149515604479536132571201203026973304072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138962118241169507353/50000000000000000000)
  centralHi := (277924236482339014707/100000000000000000000)
  directionLo := (1764820666484401639/625000000000000000)
  directionHi := (282371306637504262241/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree033.table
  base := (-6305668085686505401475737209709393075443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-13288950123100146829102293013529697600000000000000)
      constant := (126654022553491047586473309047171390901257515844256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree033.table
  base := (-12613282626565029405617488160622082786827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-9969016061544129473492892711249853200000000000000)
      constant := (95035714383195635007621948867585896851278464474844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1764820666484401639/625000000000000000)
  centralHi := (282371306637504262241/100000000000000000000)
  directionLo := (71687354359072552847/25000000000000000000)
  directionHi := (286749417436290211389/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree034.table
  base := (-12662275437388301828670876436912158837349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-13644471750489446327717001146612990400000000000000)
      constant := (133762562157281646104067834091945006083332714368304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree034.table
  base := (-1266405675176166247502368376899214062279/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-10235727084183650138413504809580582800000000000000)
      constant := (100369781743342900292724671306865543349314340181880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71687354359072552847/25000000000000000000)
  centralHi := (286749417436290211389/100000000000000000000)
  directionLo := (291061680727525819029/100000000000000000000)
  directionHi := (29106168072752581903/10000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree035.table
  base := (-12658198024946670995128453515524589253263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-13999993377878745826331709279696283200000000000000)
      constant := (141071536857308097779371763467713390080291393896848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree035.table
  base := (-3164956845134738623206561958905450454091/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-10502438106823170803334116907911312400000000000000)
      constant := (105854247006536872048983426370764674294349345533808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291061680727525819029/100000000000000000000)
  centralHi := (29106168072752581903/10000000000000000000)
  directionLo := (295310981129744873683/100000000000000000000)
  directionHi := (73827745282436218421/25000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree036.table
  base := (-12601643945036218273225733355981421044557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-14355515005268045324946417412779576000000000000000)
      constant := (148580371181812748971155325740869306274382661597872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree036.table
  base := (-12603133594696959245038269063257533555299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-10769149129462691468254729006242042000000000000000)
      constant := (111488678726848827246569791992368720812005543773628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295310981129744873683/100000000000000000000)
  centralHi := (73827745282436218421/25000000000000000000)
  directionLo := (149749999301913930721/50000000000000000000)
  directionHi := (299499998603827861443/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree037.table
  base := (-2498971191416780724613000573869392192763/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-14711036632657344823561125545862868800000000000000)
      constant := (156288557005155406140358014672258217809855627444240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree037.table
  base := (-12496217269255931197399903401586316918001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-11035860152102212133175341104572771600000000000000)
      constant := (117272695960328801705589144351670605112242560373972) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149749999301913930721/50000000000000000000)
  centralHi := (299499998603827861443/100000000000000000000)
  directionLo := (60726245644391107553/20000000000000000000)
  directionHi := (151815614110977768883/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree038.table
  base := (-12339815555427238747090322169168297357013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-15066558260046644322175833678946161600000000000000)
      constant := (164195645394621001947042460593816349319719081356848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree038.table
  base := (-6170529530448360181879499930230601528363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-11302571174741732798095953202903501200000000000000)
      constant := (123205962149776813642924628861478304761281319039672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60726245644391107553/20000000000000000000)
  centralHi := (151815614110977768883/50000000000000000000)
  directionLo := (153853498773552113781/50000000000000000000)
  directionHi := (307706997547104227563/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree039.table
  base := (-12138274424552317048958084475003161296313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-15422079887435943820790541812029454400000000000000)
      constant := (172301239483835812219279707570833435568159181489648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree039.table
  base := (-3034852466008909172426261641131974518827/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-11569282197381253463016565301234230800000000000000)
      constant := (129288179779662829796345110044170104596466367915376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153853498773552113781/50000000000000000000)
  centralHi := (307706997547104227563/100000000000000000000)
  directionLo := (31172948196687134199/10000000000000000000)
  directionHi := (311729481966871341991/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree040.table
  base := (-11891781959001041995060821521750525330133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-15777601514825243319405249945112747200000000000000)
      constant := (180604988237782860466416890488044954167784574840368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree040.table
  base := (-11892818330691764996964692911348475886359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-11835993220020774127937177399564960400000000000000)
      constant := (135519085699895100978238777172467278762680781183948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31172948196687134199/10000000000000000000)
  centralHi := (311729481966871341991/100000000000000000000)
  directionLo := (39462589783556068601/12500000000000000000)
  directionHi := (315700718268448548809/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree041.table
  base := (-11601709361583913391505678476915045156291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-16133123142214542818019958078196040000000000000000)
      constant := (189106580993045667452790898822580517391108608429136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree041.table
  base := (-11602654967992054380752162394430141296293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-12102704242660294792857789497895690000000000000000)
      constant := (141898447031123227544894064295907838186607344557796) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39462589783556068601/12500000000000000000)
  centralHi := (315700718268448548809/100000000000000000000)
  directionLo := (319622616695212420263/100000000000000000000)
  directionHi := (39952827086901552533/12500000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree042.table
  base := (-1126927076335547529290000153483315667231/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-16488644769603842316634666211279332800000000000000)
      constant := (197805742672809505305902768562387152835465804473760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree042.table
  base := (-11270133256940854288687473524195592441927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-12369415265299815457778401596226419600000000000000)
      constant := (148426057576194010961350698095803218863606291932044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319622616695212420263/100000000000000000000)
  centralHi := (39952827086901552533/12500000000000000000)
  directionLo := (16174848584374371157/5000000000000000000)
  directionHi := (323496971687487423141/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree043.table
  base := (-10895541748749869013411577297312833328163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-16844166396993141815249374344362625600000000000000)
      constant := (206702229589756594659696532465264274747270071367248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree043.table
  base := (-2724082043996961765570985604265462294901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-12636126287939336122699013694557149200000000000000)
      constant := (155101734672589224908182947308646756685971552083088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16174848584374371157/5000000000000000000)
  centralHi := (323496971687487423141/100000000000000000000)
  directionLo := (327325471478856037907/100000000000000000000)
  directionHi := (81831367869714009477/25000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree044.table
  base := (-10481475617752918335458175493276612346819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-17199688024382441313864082477445918400000000000000)
      constant := (215795825761664424116360112963777846086744901561424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree044.table
  base := (-524109623068994148271802650067796259741/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-12902837310578856787619625792887878800000000000000)
      constant := (161925316429433655479937526047323718841079890505040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327325471478856037907/100000000000000000000)
  centralHi := (81831367869714009477/25000000000000000000)
  directionLo := (165554853346810521411/50000000000000000000)
  directionHi := (331109706693621042823/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree045.table
  base := (-10027917672709760366664155801930096203723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-17555209651771740812478790610529211200000000000000)
      constant := (225086339674547981871539396112738472985104382253008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree045.table
  base := (-401142835679289828263309826120119839067/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-13169548333218377452540237891218608400000000000000)
      constant := (168896659300189302130081128848985817133567543303100) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165554853346810521411/50000000000000000000)
  centralHi := (331109706693621042823/100000000000000000000)
  directionLo := (5232049657337900031/1562500000000000000)
  directionHi := (66970235613925120397/20000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree046.table
  base := (-476780888962892796323602102959613895393/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-17910731279161040311093498743612504000000000000000)
      constant := (234573601436820808118287427939295896061275775546560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree046.table
  base := (-9536212848127249875531947081281768811683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-13436259355857898117460849989549338000000000000000)
      constant := (176015635948630354649579604676717047204091674546876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5232049657337900031/1562500000000000000)
  centralHi := (66970235613925120397/20000000000000000000)
  directionLo := (169275651706393137559/50000000000000000000)
  directionHi := (338551303412786275119/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree047.table
  base := (-4502620709016437054874729466966470111711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-18266252906550339809708206876695796800000000000000)
      constant := (244257460275390626027621766876413872708311147546912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree047.table
  base := (-9005783361190727789924260304010457699617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-13702970378497418782381462087880067600000000000000)
      constant := (183282133371276747980831522090586817994472864536724) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169275651706393137559/50000000000000000000)
  centralHi := (338551303412786275119/100000000000000000000)
  directionLo := (342211423874739795127/100000000000000000000)
  directionHi := (42776427984342474391/12500000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree048.table
  base := (-843737941545898352412009560956457693909/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-18621774533939639308322915009779089600000000000000)
      constant := (254137782331025181308847274888242916386063726300640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree048.table
  base := (-8437872842248849640592297319712480497231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-13969681401136939447302074186210797200000000000000)
      constant := (190696051244281065622537456651268897337000060095532) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342211423874739795127/100000000000000000000)
  centralHi := (42776427984342474391/12500000000000000000)
  directionLo := (172916404816212556439/50000000000000000000)
  directionHi := (345832809632425112879/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree049.table
  base := (-3916278258730527465051159540835046279263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-18977296161328938806937623142862382400000000000000)
      constant := (264214448715868822261610374306599408194010071185696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree049.table
  base := (-7833005653683892163223102198660751242041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-14236392423776460112222686284541526800000000000000)
      constant := (198257300466923904200512245857017137164948874420852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172916404816212556439/50000000000000000000)
  centralHi := (345832809632425112879/100000000000000000000)
  directionLo := (349416665037799171683/100000000000000000000)
  directionHi := (87354166259449792921/25000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree050.table
  base := (-8989048685970421825704902528211150293/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-19332817788718238305552331275945675200000000000000)
      constant := (274487353800784406032846882749131271405334022182400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree050.table
  base := (-7191647666439755384181355114951555163493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-14503103446415980777143298382872256400000000000000)
      constant := (205965801877469689948046749785077703624865397876196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349416665037799171683/100000000000000000000)
  centralHi := (87354166259449792921/25000000000000000000)
  directionLo := (1764820666484401639/500000000000000000)
  directionHi := (352964133296880327801/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree051.table
  base := (-101778766909851679908888896479764400797/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-19688339416107537804167039409028968000000000000000)
      constant := (284956403704344083257046505799863140348639483194368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree051.table
  base := (-6514212927309066340284498843336545282691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-14769814469055501442063910481202986000000000000000)
      constant := (213821485120247732783597317893390848639051311982652) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1764820666484401639/500000000000000000)
  centralHi := (352964133296880327801/100000000000000000000)
  directionLo := (356476300729653362161/100000000000000000000)
  directionHi := (178238150364826681081/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree052.table
  base := (-5800731326479158526126530024059424970049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-20043861043496837302781747542112260800000000000000)
      constant := (295621514958886665680803573631615857622100579547504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree052.table
  base := (-2900534772382432146205735058657413061837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-15036525491695022106984522579533715600000000000000)
      constant := (221824287645519769892631780189716708830597935109128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356476300729653362161/100000000000000000000)
  centralHi := (178238150364826681081/50000000000000000000)
  directionLo := (44994275081978939931/12500000000000000000)
  directionHi := (359954200655831519449/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree053.table
  base := (-5052237326960225556482958825457703737459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (273477303)
      previous := (0)
      next := (243769625)
      square := (6343614624984202406721145339468800000000000000)
      linear := (-384894012658228996252763314626331200000000000000)
      constant := (5782690817588222291938445964116710222709629865488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree053.table
  base := (-5052544888090318159157478185828312401409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32060760000000000000000000000000000000000000000
      center := (205161671)
      previous := (0)
      next := (182773525)
      square := (4757710968738151805040859004601600000000000000)
      linear := (-288740311591217788149153484488008400000000000000)
      constant := (4339134977849684911438412675611145607489340238916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44994275081978939931/12500000000000000000)
  centralHi := (359954200655831519449/100000000000000000000)
  directionLo := (36339881694587143819/10000000000000000000)
  directionHi := (363398816945871438191/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree054.table
  base := (-4268650562864067457880546764517406583429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-20754904298275436300011163808278846400000000000000)
      constant := (317539632785897903200463700084099813309390924167984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree054.table
  base := (-4268930182618032994928054987639890149517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-15569947536974063436825746776195174800000000000000)
      constant := (238271034176189202799041954424959512332096848139524) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36339881694587143819/10000000000000000000)
  centralHi := (363398816945871438191/100000000000000000000)
  directionLo := (366811087271826253927/100000000000000000000)
  directionHi := (45851385908978281741/12500000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree055.table
  base := (-138009216502251328298853448765630057791/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-21110425925664735798625871941362139200000000000000)
      constant := (328792514554589161659138564649098255796079869328400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree055.table
  base := (-3450484573516418773238757294168368571429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-15836658559613584101746358874525904400000000000000)
      constant := (246714884661514914746814838346274477738891321461988) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366811087271826253927/100000000000000000000)
  centralHi := (45851385908978281741/12500000000000000000)
  directionLo := (370191906088476891907/100000000000000000000)
  directionHi := (92547976522119222977/25000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree056.table
  base := (-519441550173944000553830649671995993669/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-21465947553054035297240580074445432000000000000000)
      constant := (340241206330623141439674675283860960972985922395120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree056.table
  base := (-649359680385022927639741067485232076333/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-16103369582253104766666970972856634000000000000000)
      constant := (255305666087667231751690359663798209222155383346704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370191906088476891907/100000000000000000000)
  centralHi := (92547976522119222977/25000000000000000000)
  directionLo := (373542127371599216513/100000000000000000000)
  directionHi := (186771063685799608257/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree057.table
  base := (-1709788133832781377865679600189762827253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-21821469180443334795855288207528724800000000000000)
      constant := (351885661542670223936585064387650278420738875427888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree057.table
  base := (-1709997986310490604951852927299465539433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-16370080604892625431587583071187363600000000000000)
      constant := (264043343559522809620823740867470590752223430669876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373542127371599216513/100000000000000000000)
  centralHi := (186771063685799608257/50000000000000000000)
  directionLo := (376862567137120174179/100000000000000000000)
  directionHi := (18843128356856008709/5000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree058.table
  base := (-788154619563204941076570196541898043273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-22176990807832634294469996340612017600000000000000)
      constant := (363725838716588265366967244295826962330023760109808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree058.table
  base := (-394172622926935709206305250736223684399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-16636791627532146096508195169518093200000000000000)
      constant := (272927886002076550303905668816041888156970579917656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376862567137120174179/100000000000000000000)
  centralHi := (18843128356856008709/5000000000000000000)
  directionLo := (76030801152443676919/20000000000000000000)
  directionHi := (95038501440554596149/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree059.table
  base := (20941216488222492622591786427710665367/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-22532512435221933793084704473695310400000000000000)
      constant := (375761700909055222955668160316372991231001493378944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree059.table
  base := (81717092206645589822755925103874611/4882812500000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-16903502650171666761428807267848822800000000000000)
      constant := (281959265735881307538756411367457284860376486109184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76030801152443676919/20000000000000000000)
  centralHi := (95038501440554596149/25000000000000000000)
  directionLo := (76683438025414882109/20000000000000000000)
  directionHi := (191708595063537205273/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree060.table
  base := (231423928460678650213816018124898884447/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-22888034062611233291699412606778603200000000000000)
      constant := (387993215205433236337793396281196352504934479323440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree060.table
  base := (578481219336386755041629474239940422489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-17170213672811187426349419366179552400000000000000)
      constant := (291137458100646614543686213793229862870377015375384) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76683438025414882109/20000000000000000000)
  centralHi := (191708595063537205273/50000000000000000000)
  directionLo := (193326417796961652673/50000000000000000000)
  directionHi := (386652835593923305347/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree061.table
  base := (1090242824642478228501298426852920308911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-23243555690000532790314120739861896000000000000000)
      constant := (400420352274383428965080170373805589270966782910688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree061.table
  base := (2180342931708008689700132989561338711747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-17436924695450708091270031464510282000000000000000)
      constant := (300462441121386519789476799569948679204294957662916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193326417796961652673/50000000000000000000)
  centralHi := (386652835593923305347/100000000000000000000)
  directionLo := (389861627838264999727/100000000000000000000)
  directionHi := (24366351739891562483/6250000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree062.table
  base := (161875618101824450805127579790137789321/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-23599077317389832288928828872945188800000000000000)
      constant := (413043085972650968644775801445856156401622961679680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree062.table
  base := (3237382819788819824553188911618683789791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-17703635718090228756190643562841011600000000000000)
      constant := (309934195212181863755253045491741962512252012416148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (389861627838264999727/100000000000000000000)
  centralHi := (24366351739891562483/6250000000000000000)
  directionLo := (393044224545511164653/100000000000000000000)
  directionHi := (196522112272755582327/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree063.table
  base := (4328096912752443062689129422509652770419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-23954598944779131787543537006028481600000000000000)
      constant := (425861392994227675906230441836652049597767219852976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree063.table
  base := (4327979350966633196587981899502014979139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-17970346740729749421111255661171741200000000000000)
      constant := (319552702913213163843135640081205356475341676573892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393044224545511164653/100000000000000000000)
  centralHi := (196522112272755582327/50000000000000000000)
  directionLo := (396201256984960307897/100000000000000000000)
  directionHi := (198100628492480153949/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree064.table
  base := (2726073790731859651419774368713467156151/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-24310120572168431286158245139111774400000000000000)
      constant := (438875252558789340816968455380511539440225521584608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree064.table
  base := (1090408182241155942999038529724555512299/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-18237057763369270086031867759502470800000000000000)
      constant := (329317948657237685896877347640803624170242125111860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396201256984960307897/100000000000000000000)
  centralHi := (198100628492480153949/50000000000000000000)
  directionLo := (399333331471770481923/100000000000000000000)
  directionHi := (99833332867942620481/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree065.table
  base := (3304791287180966936747601427500304132883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-24665642199557730784772953272195067200000000000000)
      constant := (452084646134909565471105318436283035730336695591264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree065.table
  base := (6609485803519564310964008080630724635309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-18503768786008790750952479857833200400000000000000)
      constant := (339229918562137769201368235263934568749141265686652) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399333331471770481923/100000000000000000000)
  centralHi := (99833332867942620481/25000000000000000000)
  directionLo := (201220515363259664903/50000000000000000000)
  directionHi := (402441030726519329807/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree066.table
  base := (7800328938106970082169355825065783511849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-25021163826947030283387661405278360000000000000000)
      constant := (465489557194082347199115699622963171490323125479696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree066.table
  base := (7800241163028124819988467179401418444169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-18770479808648311415873091956163930000000000000000)
      constant := (349288600246565257601254980436649385048109801254732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201220515363259664903/50000000000000000000)
  centralHi := (402441030726519329807/100000000000000000000)
  directionLo := (81104983028197135161/20000000000000000000)
  directionHi := (202762457570492837903/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree067.table
  base := (902432159466003453152344066505260551219/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-25376685454336329782002369538361652800000000000000)
      constant := (479089970992051245952001226801495799607087071361760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree067.table
  base := (4512120996242128376832098390293738782999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-19037190831287832080793704054494659600000000000000)
      constant := (359493982666056091692537209586793388719418884003944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81104983028197135161/20000000000000000000)
  centralHi := (202762457570492837903/50000000000000000000)
  directionLo := (408585523957939546941/100000000000000000000)
  directionHi := (204292761978969773471/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree068.table
  base := (5140751241495026561643802185545609124253/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-25732207081725629280617077671444945600000000000000)
      constant := (492885874374352064554033520353641643037035663320224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree068.table
  base := (1028143030461885746461323800181827250297/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-19303901853927352745714316152825389200000000000000)
      constant := (369846055967295907371632291058573548951161298423160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408585523957939546941/100000000000000000000)
  centralHi := (204292761978969773471/50000000000000000000)
  directionLo := (411623376371974711951/100000000000000000000)
  directionHi := (25726461023248419497/6250000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree069.table
  base := (2892954948897198523809447712264142446371/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-26087728709114928779231785804528238400000000000000)
      constant := (506877255603335650514904413076868051499563954988736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree069.table
  base := (11571754359245037106925539268435115253827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-19570612876566873410634928251156118800000000000000)
      constant := (380344811358487219216910581382839268070344018601156) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411623376371974711951/100000000000000000000)
  centralHi := (25726461023248419497/6250000000000000000)
  directionLo := (103659743139436942311/25000000000000000000)
  directionHi := (82927794511549553849/20000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree070.table
  base := (12895227299126955050572279495316120649227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-26443250336504228277846493937611531200000000000000)
      constant := (521064104204253902161160826199363524629079104629808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree070.table
  base := (6447583992228311760738239193088370942107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-19837323899206394075555540349486848400000000000000)
      constant := (390990240994006093829376486051607862147398184065992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103659743139436942311/25000000000000000000)
  centralHi := (82927794511549553849/20000000000000000000)
  directionLo := (417632794631390346879/100000000000000000000)
  directionHi := (652551241611547417/156250000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree071.table
  base := (14251683729813385343209295305629694030523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31910240000000000000000000000000000000000000000
      center := (204145029)
      previous := (0)
      next := (181968875)
      square := (4735374297523418697974939478758400000000000000)
      linear := (-377447492449204616569876085502744000000000000000)
      constant := (7541498744060150973396551067197856288764055625552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree071.table
  base := (14251629972486545341951846807613947805997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23932680000000000000000000000000000000000000000
      center := (153148853)
      previous := (0)
      next := (136436575)
      square := (3551530723142564023481204609068800000000000000)
      linear := (-283155421434449503386988062645318000000000000000)
      constant := (5658906167207678606913312167088524317637762828196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417632794631390346879/100000000000000000000)
  centralHi := (652551241611547417/156250000000000000)
  directionLo := (420605307550327310209/100000000000000000000)
  directionHi := (42060530755032731021/10000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree072.table
  base := (7820576127551665515153087269108564193359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-27154293591282827275075910203778116800000000000000)
      constant := (550024167130505166710582216448020395946409987765472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree072.table
  base := (7820551770937056549416984844527766901323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-20370745944485435405396764546148307600000000000000)
      constant := (412721095741724087844377927326586769708368160086088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420605307550327310209/100000000000000000000)
  centralHi := (42060530755032731021/10000000000000000000)
  directionLo := (5294461999453204917/1250000000000000000)
  directionHi := (423556959956256393361/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree073.table
  base := (17063599994357111939686437097923233881261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-27509815218672126773690618336861409600000000000000)
      constant := (564797365661430609769938609334720785852562907089744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree073.table
  base := (17063555858545560058431390338608654268033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-20637456967124956070317376644479037200000000000000)
      constant := (423806509024710412144986988194151888131575022930924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5294461999453204917/1250000000000000000)
  centralHi := (423556959956256393361/100000000000000000000)
  directionLo := (213244092482808383653/50000000000000000000)
  directionHi := (426488184965616767307/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree074.table
  base := (1851899759189368164581691021886967751617/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-27865336846061426272305326469944702400000000000000)
      constant := (579765999770144572649505974167612412161671478923680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree074.table
  base := (578717425289220868011353818929132833907/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-20904167989764476735237988742809766800000000000000)
      constant := (435038572739737977260083358011077520661403667308672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213244092482808383653/50000000000000000000)
  centralHi := (426488184965616767307/100000000000000000000)
  directionLo := (21469970045574498779/5000000000000000000)
  directionHi := (429399400911489975581/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree075.table
  base := (20007318836627790137607047384815410883909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-28220858473450725770920034603027995200000000000000)
      constant := (594930063518192706332255606739137923030729453129936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree075.table
  base := (20007282621577596495493729043729255371029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-21170879012403997400158600841140496400000000000000)
      constant := (446417282439535242756153854026443393255575140126812) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21469970045574498779/5000000000000000000)
  centralHi := (429399400911489975581/100000000000000000000)
  directionLo := (216145506020265695549/50000000000000000000)
  directionHi := (432291012040531391099/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree076.table
  base := (4305708064627387414144788129601944320987/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-28576380100840025269534742736111288000000000000000)
      constant := (610289551602779200877734512348471826345101293344240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree076.table
  base := (2691063440662767533813234654800403002463/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-21437590035043518065079212939471226000000000000000)
      constant := (457942634152988559715050199762189476507166415639712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216145506020265695549/50000000000000000000)
  centralHi := (432291012040531391099/100000000000000000000)
  directionLo := (27197713073013718107/6250000000000000000)
  directionHi := (435163409168219489713/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree077.table
  base := (11541320574792717012477601487316525993723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-28931901728229324768149450869194580800000000000000)
      constant := (625844459288327644153757884334937423666048339813984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree077.table
  base := (721331607832968602868503111065693756081/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-21704301057683038729999825037801955600000000000000)
      constant := (469614624333863656484372534517284636076327067272576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27197713073013718107/6250000000000000000)
  centralHi := (435163409168219489713/100000000000000000000)
  directionLo := (43801697029542996043/10000000000000000000)
  directionHi := (438016970295429960431/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree078.table
  base := (24669602648446840237810669458708468677189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-29287423355618624266764159002277873600000000000000)
      constant := (641594782345472768749680129164030675211203242959056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree078.table
  base := (2466957575929642105075508864460978726451/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-21971012080322559394920437136132685200000000000000)
      constant := (481433249815096045803906252392120483720634111626280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43801697029542996043/10000000000000000000)
  centralHi := (438016970295429960431/100000000000000000000)
  directionLo := (440852061189088612839/100000000000000000000)
  directionHi := (11021301529727215321/2500000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree079.table
  base := (13144704073210405817276751668127809042333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-29642944983007923765378867135361166400000000000000)
      constant := (657540516996666564107798491010097582268453229896864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree079.table
  base := (13144691902244350954890067090460423203091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-22237723102962080059841049234463414800000000000000)
      constant := (493398507768038295448420548724959919028814957177096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440852061189088612839/100000000000000000000)
  centralHi := (11021301529727215321/2500000000000000000)
  directionLo := (443669035929428242177/100000000000000000000)
  directionHi := (221834517964714121089/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree080.table
  base := (27942042750343029739681615595366407562723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-29998466610397223263993575268444459200000000000000)
      constant := (673681659867673451117986058828951559168176572482992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree080.table
  base := (27942020717236103639820815579140709714817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-22504434125601600724761661332794144400000000000000)
      constant := (505510395666120495934366839224046615892101006288876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443669035929428242177/100000000000000000000)
  centralHi := (221834517964714121089/50000000000000000000)
  directionLo := (1744016552445966677/390625000000000000)
  directionHi := (446468237426167469313/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree081.table
  base := (29627493156243513437190310515573938676909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-30353988237786522762608283401527752000000000000000)
      constant := (690018207944310016923771871081466397258570685401936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree081.table
  base := (29627473215553723830975884105315134673091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-22771145148241121389682273431124874000000000000000)
      constant := (517768911252440836778872616424774636962744739748548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1744016552445966677/390625000000000000)
  centralHi := (446468237426167469313/100000000000000000000)
  directionLo := (112312499476435448041/25000000000000000000)
  directionHi := (89849999581148358433/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree082.table
  base := (31345747479024667437580216029066327318301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-30709509865175822261222991534611044800000000000000)
      constant := (706550158533856413032469287225656564712583343245904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree082.table
  base := (31345729434338161606738303480065916476803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-23037856170880642054602885529455603600000000000000)
      constant := (530174052510856885675304827166282463101416980716484) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112312499476435448041/25000000000000000000)
  centralHi := (89849999581148358433/20000000000000000000)
  directionLo := (22600731968577332049/5000000000000000000)
  directionHi := (452014639371546640981/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree083.table
  base := (16548397550255317072124217080746580696383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-31065031492565121759837699667694337600000000000000)
      constant := (723277509230630005599473013482217109522653470999264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree083.table
  base := (3309677877359302807940735006425790758649/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-23304567193520162719523497627786333200000000000000)
      constant := (542725817640195759431188700230740709872132966201720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22600731968577332049/5000000000000000000)
  centralHi := (452014639371546640981/100000000000000000000)
  directionLo := (227381237019498665147/50000000000000000000)
  directionHi := (90952494807799466059/20000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree084.table
  base := (34880626533868063521526840527606773946143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-31420553119954421258452407800777630400000000000000)
      constant := (740200257885268178443323583143817982553954908450672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree084.table
  base := (17440305881505378700833479700141806644941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-23571278216159683384444109726117062800000000000000)
      constant := (555424205031243590674004751588533991745384501320696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227381237019498665147/50000000000000000000)
  centralHi := (90952494807799466059/20000000000000000000)
  directionLo := (114373451186767464487/25000000000000000000)
  directionHi := (457493804747069857949/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree085.table
  base := (36697233302618969573306008373587719191087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-31776074747343720757067115933860923200000000000000)
      constant := (757318402577317158660268311005223907841125363419248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree085.table
  base := (9174304985283157467683383081035203471111/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-23837989238799204049364721824447792400000000000000)
      constant := (568269213246212153913572434824575946952815282132432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114373451186767464487/25000000000000000000)
  centralHi := (457493804747069857949/100000000000000000000)
  directionLo := (23010446267392905399/5000000000000000000)
  directionHi := (460208925347858107981/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree086.table
  base := (19273303916331066900540987313953061777401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-32131596374733020255681824066944216000000000000000)
      constant := (774631941590768093817591319238232931810734033304608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree086.table
  base := (3854659574750461470079527511448357884087/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-24104700261438724714285333922778522000000000000000)
      constant := (581260841000413767637992176323417808089338519684360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23010446267392905399/5000000000000000000)
  centralHi := (460208925347858107981/100000000000000000000)
  directionLo := (462908121075565917809/100000000000000000000)
  directionHi := (46290812107556591781/10000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree087.table
  base := (40428743355893392391537371938383699388817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-32487118002122319754296532200027508800000000000000)
      constant := (792140873392221003608088473885374221323053526881168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree087.table
  base := (40428732426420427360605849264932498825033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-24371411284078245379205946021109251600000000000000)
      constant := (594399087145905119407369568878481094983457224526924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462908121075565917809/100000000000000000000)
  centralHi := (46290812107556591781/10000000000000000000)
  directionLo := (465591668896245557743/100000000000000000000)
  directionHi := (29099479306015347359/6250000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree088.table
  base := (8468726764833922897115234432780801480977/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-32842639629511619252911240333110801600000000000000)
      constant := (809845196611392226125297135815336342314086768409040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree088.table
  base := (8468724788199516811537894256297398808593/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-24638122306717766044126558119439981200000000000000)
      constant := (607683950656886894778009996217576303283404531933020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465591668896245557743/100000000000000000000)
  centralHi := (29099479306015347359/6250000000000000000)
  directionLo := (18730393513579857993/4000000000000000000)
  directionHi := (234129918919748224913/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree089.table
  base := (22145636916249228722032270561465840511229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-33198161256900918751525948466194094400000000000000)
      constant := (827744910023712081121600647338063015259713569206432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree089.table
  base := (11072816224117359363951298537346624763789/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-24904833329357286709047170217770710800000000000000)
      constant := (621115430616669404447778598727314771775272191376368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18730393513579857993/4000000000000000000)
  centralHi := (234129918919748224913/50000000000000000000)
  directionLo := (235456444656624269103/50000000000000000000)
  directionHi := (470912889313248538207/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree090.table
  base := (4627165855045802555358355708003638464737/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-33553682884290218250140656599277387200000000000000)
      constant := (845840012534787122443360808460410770724092233688480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree090.table
  base := (46271650471698146716560687772512006593063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-25171544351996807373967782316101440400000000000000)
      constant := (634693526206035129233874531418118523814642635691764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235456444656624269103/50000000000000000000)
  centralHi := (470912889313248538207/100000000000000000000)
  directionLo := (118387769350668205803/25000000000000000000)
  directionHi := (473551077402672823213/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree091.table
  base := (3017798978809942931724508333283212634303/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-33909204511679517748755364732360680000000000000000)
      constant := (864130503166525940300548595291920462235754413364992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree091.table
  base := (24142388179010998468627070807805831481591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-25438255374636328038888394414432170000000000000000)
      constant := (648418236692847532574072879964565798931156374773096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118387769350668205803/25000000000000000000)
  centralHi := (473551077402672823213/100000000000000000000)
  directionLo := (3809397193233491827/800000000000000000)
  directionHi := (59521831144273309797/12500000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree092.table
  base := (25165322652779522202044624603776102883771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-34264726139068817247370072865443972800000000000000)
      constant := (882616381044749346664952092778188002959858710953568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree092.table
  base := (25165319352323481424904058669883364108841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-25704966397275848703809006512762899600000000000000)
      constant := (662289561422771884284538682383062573505673350899096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3809397193233491827/800000000000000000)
  centralHi := (59521831144273309797/12500000000000000000)
  directionLo := (119695961211362762387/25000000000000000000)
  directionHi := (478783844845451049549/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree093.table
  base := (26204620017811379758725686705452561415407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-34620247766458116745984780998527265600000000000000)
      constant := (901297645388125239442791460383172254916001354361056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree093.table
  base := (52409234069878257541348584830754425829083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-25971677419915369368729618611093629200000000000000)
      constant := (676307499810988426416008524168067041706853364740324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119695961211362762387/25000000000000000000)
  centralHi := (478783844845451049549/100000000000000000000)
  directionLo := (3851031185937591353/800000000000000000)
  directionHi := (240689449121099459563/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree094.table
  base := (54520564768701784867159707438200343118181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-34975769393847416244599489131610558400000000000000)
      constant := (920174295498285763454934642194887506830582878921424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree094.table
  base := (5452055937756401179780848864794408734599/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-26238388442554890033650230709424358800000000000000)
      constant := (690472051334791194915637365131118806752439758467720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3851031185937591353/800000000000000000)
  centralHi := (240689449121099459563/50000000000000000000)
  directionLo := (483960036842664995381/100000000000000000000)
  directionHi := (241980018421332497691/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree095.table
  base := (11332923349914325955038334746105968812173/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-35331291021236715743214197264693851200000000000000)
      constant := (939246330750999807966346049668537837823127914978960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree095.table
  base := (56664611878191249330039245949400406117051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-26505099465194410698570842807755088400000000000000)
      constant := (704783215526977368840057163682390217891432911299428) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483960036842664995381/100000000000000000000)
  centralHi := (241980018421332497691/50000000000000000000)
  directionLo := (121631870527586749401/25000000000000000000)
  directionHi := (97305496422069399521/20000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree096.table
  base := (11768278703085459470193259174294548058757/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-35686812648626015241828905397777144000000000000000)
      constant := (958513750588287613456784064656258702103249683994640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree096.table
  base := (1838793409816715397519028505862989277851/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-26771810487833931363491454906085818000000000000000)
      constant := (719240991969942310970840881252385220103510316858496) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121631870527586749401/25000000000000000000)
  centralHi := (97305496422069399521/20000000000000000000)
  directionLo := (489081449695768338569/100000000000000000000)
  directionHi := (48908144969576833857/10000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree097.table
  base := (61050892864791320975658761481827986721911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-36042334276015314740443613530860436800000000000000)
      constant := (977976554511376492294018000363125637534592252207344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree097.table
  base := (30525444444307241489486089839268976051539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-27038521510473452028412067004416547600000000000000)
      constant := (733845380290404630645544226333545733396321878802184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489081449695768338569/100000000000000000000)
  centralHi := (48908144969576833857/10000000000000000000)
  directionLo := (491622149647872084113/100000000000000000000)
  directionHi := (245811074823936042057/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree098.table
  base := (63293112829736627101051145200784734254369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-36397855903404614239058321663943729600000000000000)
      constant := (997634742074407565420156729238123162514591264453776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree098.table
  base := (63293109237961356593497327870155740571613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-27305232533112972693332679102747277200000000000000)
      constant := (748596380154693766240221135380544675513770360191164) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (491622149647872084113/100000000000000000000)
  centralHi := (245811074823936042057/50000000000000000000)
  directionLo := (494149786615632458921/100000000000000000000)
  directionHi := (247074893307816229461/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree099.table
  base := (65568051651069411643839232033142978915081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-36753377530793913737673029797027022400000000000000)
      constant := (1017488312878813127722040607077341417121615737739024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree099.table
  base := (65568048406841849302182514016805815963927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-27571943555752493358253291201078006800000000000000)
      constant := (763493991264539861706801131934301866230785250683956) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494149786615632458921/100000000000000000000)
  centralHi := (247074893307816229461/50000000000000000000)
  directionLo := (496664560040431564233/100000000000000000000)
  directionHi := (248332280020215782117/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree100.table
  base := (33937853878077708546084059055863087839619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-37108899158183213236287737930110315200000000000000)
      constant := (1037537266568292909414751474804972826469467197939552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree100.table
  base := (67875704826120263400026551947813741575827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-27838654578392014023173903299408736400000000000000)
      constant := (778538213353312197084055468698290751134832439617156) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (496664560040431564233/100000000000000000000)
  centralHi := (248332280020215782117/50000000000000000000)
  directionLo := (124791666084928275601/25000000000000000000)
  directionHi := (99833332867942620481/20000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree101.table
  base := (70216079739107049922287212686303786258269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-37464420785572512734902446063193608000000000000000)
      constant := (1057781602824325215789495510359047771180111466999376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree101.table
  base := (14043215418615871646126034869670464290589/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-28105365601031534688094515397739466000000000000000)
      constant := (793729046182658214129084730992661778619792320972460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124791666084928275601/25000000000000000000)
  centralHi := (99833332867942620481/20000000000000000000)
  directionLo := (125414072270597929073/25000000000000000000)
  directionHi := (501656289082391716293/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree102.table
  base := (36294583171539569365644670859764376402731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-37819942412961812233517154196276900800000000000000)
      constant := (1078221321362155806303886590928666304841353056689248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree102.table
  base := (36294581976873228531266007221167993753527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-28372076623671055353015127496070195600000000000000)
      constant := (809066489539500332555090591971170667054581279985512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125414072270597929073/25000000000000000000)
  centralHi := (501656289082391716293/100000000000000000000)
  directionLo := (63016702394558227893/12500000000000000000)
  directionHi := (100826723831293164629/20000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree103.table
  base := (74994966444448207406803116872145337189353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-38175464040351111732131862329360193600000000000000)
      constant := (1098856421927213507932026446919452578074611575690512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree103.table
  base := (9374370535887539053404840214972416320597/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-28638787646310576017935739594400925200000000000000)
      constant := (824550543233352348561136795410645861462049123285728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63016702394558227893/12500000000000000000)
  centralHi := (100826723831293164629/20000000000000000000)
  directionLo := (253299417464626674203/50000000000000000000)
  directionHi := (506598834929253348407/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree104.table
  base := (15486695807734856873541278103032205737289/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-38530985667740411230746570462443486400000000000000)
      constant := (1119686904291907028436412889210294858854622547347280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree104.table
  base := (77433477090957995719394244407499335291043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-28905498668950096682856351692731654800000000000000)
      constant := (840181207093921306491622029331715107861305996795204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253299417464626674203/50000000000000000000)
  centralHi := (506598834929253348407/100000000000000000000)
  directionLo := (509052112400643359251/100000000000000000000)
  directionHi := (127263028100160839813/25000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree105.table
  base := (2497021975864556504837771059667056931111/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-38886507295129710729361278595526779200000000000000)
      constant := (1140712768252762315213269535021351646257102396292608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree105.table
  base := (15980940293872519001333197998198305656921/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-29172209691589617347776963791062384400000000000000)
      constant := (855958480968964390870386940843816186716939442778940) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509052112400643359251/100000000000000000000)
  centralHi := (127263028100160839813/25000000000000000000)
  directionLo := (255746811674866045931/50000000000000000000)
  directionHi := (511493623349732091863/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree106.table
  base := (8240863820848740573265414196868878364127/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (273477303)
      previous := (0)
      next := (243769625)
      square := (6343614624984202406721145339468800000000000000)
      linear := (-740415640047528494867471447709624000000000000000)
      constant := (21923283275997436962461034429218590014268624475360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree106.table
  base := (82408636621311701727232690648165593280317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32060760000000000000000000000000000000000000000
      center := (205161671)
      previous := (0)
      next := (182773525)
      square := (4757710968738151805040859004601600000000000000)
      linear := (-555451334230738453069765582818738000000000000000)
      constant := (16450610655139125433994760315945063552641785606092) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255746811674866045931/50000000000000000000)
  centralHi := (511493623349732091863/100000000000000000000)
  directionLo := (25696176773759455357/5000000000000000000)
  directionHi := (513923535475189107141/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree107.table
  base := (21236320815816866415979661348933665389301/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-39597550549908309726590694861693364800000000000000)
      constant := (1183350640254569626415831272602664569988924988919616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree107.table
  base := (21236320457670948752758070124979767212273/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-29705631736868658677618187987723843600000000000000)
      constant := (887952858232464256764942826315484959514709338598576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25696176773759455357/5000000000000000000)
  centralHi := (513923535475189107141/100000000000000000000)
  directionLo := (103268402505935631381/20000000000000000000)
  directionHi := (258171006264839078453/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree108.table
  base := (43757318875088864415584722464458942369247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-39953072177297609225205402994776657600000000000000)
      constant := (1204962647987464371540200663638362284960313533527776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree108.table
  base := (87514636457234916615589186648183014499531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-29972342759508179342538800086054573200000000000000)
      constant := (904169961390444665360739764467704248738913712568868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103268402505935631381/20000000000000000000)
  centralHi := (258171006264839078453/50000000000000000000)
  directionLo := (259374607224318834659/50000000000000000000)
  directionHi := (518749214448637669319/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree109.table
  base := (18023340219074154969276646759269608968363/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-40308593804686908723820111127859950400000000000000)
      constant := (1226770036696535971137007708258417413564474858667760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree109.table
  base := (90116699928551670040242306769187819386559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-30239053782147700007459412184385302800000000000000)
      constant := (920533674099049228601352673354175791083061821221652) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259374607224318834659/50000000000000000000)
  centralHi := (518749214448637669319/100000000000000000000)
  directionLo := (521145297473707452183/100000000000000000000)
  directionHi := (65143162184213431523/12500000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree110.table
  base := (18550294557154694192207381457045695667447/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-40664115432076208222434819260943243200000000000000)
      constant := (1248772806265541188900996059852623600309889385483440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree110.table
  base := (92751471732858752419493743662563604368243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-30505764804787220672380024282716032400000000000000)
      constant := (937043996271316049143561939052877214333241509356804) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521145297473707452183/100000000000000000000)
  centralHi := (65143162184213431523/12500000000000000000)
  directionLo := (523530414271071159727/100000000000000000000)
  directionHi := (32720650891941947483/6250000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree111.table
  base := (23854738090661332722934739955693528263881/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-41019637059465507721049527394026536000000000000000)
      constant := (1270970956590546539825525628627779590435061219576896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree111.table
  base := (4770947570629504795950902671805240830977/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-30772475827426741337300636381046762000000000000000)
      constant := (953700927829494572796973414125644737560560341227120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523530414271071159727/100000000000000000000)
  centralHi := (32720650891941947483/6250000000000000000)
  directionLo := (262952357022484087823/50000000000000000000)
  directionHi := (525904714044968175647/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree112.table
  base := (4905956970791022243661581152944486927331/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-41375158686854807219664235527109828800000000000000)
      constant := (1293364487578623726305559609329482194402975257260480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree112.table
  base := (9811913855864239783815591151202658248343/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-31039186850066262002221248479377491600000000000000)
      constant := (970504468704069136705193189203110911285493701996040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262952357022484087823/50000000000000000000)
  centralHi := (525904714044968175647/100000000000000000000)
  directionLo := (528268342646613743863/100000000000000000000)
  directionHi := (66033542830826717983/12500000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree113.table
  base := (100852033578560315375716581286871370209393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-41730680314244106718278943660193121600000000000000)
      constant := (1315953399146683482679849574976574886534825124278672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree113.table
  base := (100852032805238481307594289754471936405981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-31305897872705782667141860577708221200000000000000)
      constant := (987454618832886141178472903577609860403191322849468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528268342646613743863/100000000000000000000)
  centralHi := (66033542830826717983/12500000000000000000)
  directionLo := (21224857707150093901/4000000000000000000)
  directionHi := (265310721339376173763/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree114.table
  base := (103617634522952677487353018730004782178847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-42086201941633406216893651793276414400000000000000)
      constant := (1338737691220433119535204548729119431583370587922288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree114.table
  base := (6476102114083478968190479334789759925867/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-31572608895345303332062472676038950800000000000000)
      constant := (1004551378160373830306710129906457186763783204772416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21224857707150093901/4000000000000000000)
  centralHi := (265310721339376173763/50000000000000000000)
  directionLo := (266482076798028210913/50000000000000000000)
  directionHi := (532964153596056421827/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree115.table
  base := (13301992744474787371062610860091455494913/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-42441723569022705715508359926359707200000000000000)
      constant := (1361717363733444626004687705210552249753785180198016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree115.table
  base := (106415941326521215484395640861381954947723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-31839319917984823996983084774369680400000000000000)
      constant := (1021794746636844840181502510658505742167321726142244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266482076798028210913/50000000000000000000)
  centralHi := (532964153596056421827/100000000000000000000)
  directionLo := (267648305900785209619/50000000000000000000)
  directionHi := (535296611801570419239/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree116.table
  base := (13655869451866741446565785614773034899283/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-42797245196412005214123068059443000000000000000000)
      constant := (1384892416626321587676118408952829740664543393129856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree116.table
  base := (10924695504734316672752747330018478255683/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-32106030940624344661903696872700410000000000000000)
      constant := (1039184724217872721740679734523021432226795578851240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267648305900785209619/50000000000000000000)
  centralHi := (535296611801570419239/100000000000000000000)
  directionLo := (537618950739388964033/100000000000000000000)
  directionHi := (268809475369694482017/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree117.table
  base := (5605533763297255093566733638774512514057/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-43152766823801304712737776192526292800000000000000)
      constant := (1408262849845954427592891411390764944029331838602560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree117.table
  base := (112110674754030216112913652320135801729583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-32372741963263865326824308971031139600000000000000)
      constant := (1056721310863734581411851740351302879165296650954324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537618950739388964033/100000000000000000000)
  centralHi := (268809475369694482017/50000000000000000000)
  directionLo := (539931300983747279173/100000000000000000000)
  directionHi := (269965650491873639587/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree118.table
  base := (23001420139845471477492682132735300145567/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-43508288451190604211352484325609585600000000000000)
      constant := (1431828663344854594231273277794790134786156265665840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree118.table
  base := (57503550118779716449021125554025495242591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-32639452985903385991744921069361869200000000000000)
      constant := (1074404506538912818904747355725066276830650829389096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (539931300983747279173/100000000000000000000)
  centralHi := (269965650491873639587/50000000000000000000)
  directionLo := (271116895162346095019/50000000000000000000)
  directionHi := (542233790324692190039/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree119.table
  base := (117936231727358985518865283696922654076057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-43863810078579903709967192458692878400000000000000)
      constant := (1455589857080559317595833315224704797186328095578128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree119.table
  base := (117936231311034826153379237764128554897737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-32906164008542906656665533167692598800000000000000)
      constant := (1092234311211649688415550552848880611600932803650636) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271116895162346095019/50000000000000000000)
  centralHi := (542233790324692190039/100000000000000000000)
  directionLo := (272263271925246378687/50000000000000000000)
  directionHi := (4356212350803942059/800000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree120.table
  base := (30224517045688038730141284868934630581759/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-44219331705969203208581900591776171200000000000000)
      constant := (1479546431015099445459557996340068346015377648465344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree120.table
  base := (60449033903671894063766998615946641305127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-33172875031182427321586145266023328400000000000000)
      constant := (1110210724853549076730776518592182280860711493275112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272263271925246378687/50000000000000000000)
  centralHi := (4356212350803942059/800000000000000000)
  directionLo := (273404842013470460887/50000000000000000000)
  directionHi := (21872387361077636871/4000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree121.table
  base := (30973152478888235492472093080248305549681/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-44574853333358502707196608724859464000000000000000)
      constant := (1503698385114523667681484686766083131987015734789696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree121.table
  base := (3871644049283185151014532409207989504897/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-33439586053821947986506757364354058000000000000000)
      constant := (1128333747439220487791306234815380782115194053475712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273404842013470460887/50000000000000000000)
  centralHi := (21872387361077636871/4000000000000000000)
  directionLo := (109816666154736882529/20000000000000000000)
  directionHi := (274541665386842206323/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree122.table
  base := (2538397135835276871193487577830616435339/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-44930374960747802205811316857942756800000000000000)
      constant := (1528045719348473147628406678447505432678862249832800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree122.table
  base := (126919856486579921173133950839004651224867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-33706297076461468651427369462684787600000000000000)
      constant := (1146603378945960755816499762745828900837562084670276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109816666154736882529/20000000000000000000)
  centralHi := (274541665386842206323/50000000000000000000)
  directionLo := (137836900384431637057/25000000000000000000)
  directionHi := (551347601537726548229/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree123.table
  base := (25995961738313036355373132682328714750767/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-45285896588137101704426024991026049600000000000000)
      constant := (1552588433689801215079932588233922323353892287969840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree123.table
  base := (32494952104107222017499607311721187741653/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-33973008099100989316347981561015517200000000000000)
      constant := (1165019619353469484891054219889391553466521671329136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137836900384431637057/25000000000000000000)
  centralHi := (551347601537726548229/100000000000000000000)
  directionLo := (8650040802565943667/1562500000000000000)
  directionHi := (553602611364220394689/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree124.table
  base := (13307246550781431176593626403557882707893/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-45641418215526401203040733124109342400000000000000)
      constant := (1577326528114233342703882764867359252468150802226720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree124.table
  base := (66536232629891570473999034761084302837181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-34239719121740509981268593659346246800000000000000)
      constant := (1183582468643594638049487024380453908834119898646136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8650040802565943667/1562500000000000000)
  centralHi := (553602611364220394689/100000000000000000000)
  directionLo := (555848472964678029413/100000000000000000000)
  directionHi := (277924236482339014707/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree125.table
  base := (136197827144703783142208163260950106935167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-45996939842915700701655441257192635200000000000000)
      constant := (1602260002600063135477758716533116213836320588211568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree125.table
  base := (136197826921121594554560371569963051403493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-34506430144380030646189205757676976400000000000000)
      constant := (1202291926800105078768920164785861528079549776843804) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555848472964678029413/100000000000000000000)
  centralHi := (277924236482339014707/50000000000000000000)
  directionLo := (558085296782709336641/100000000000000000000)
  directionHi := (279042648391354668321/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree126.table
  base := (139355893516561606179838546606835397130941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-46352461470305000200270149390275928000000000000000)
      constant := (1627388857127880515752213276503425159056899835024464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree126.table
  base := (27871178663006191352568690363276655580641/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-34773141167019551311109817856007706000000000000000)
      constant := (1221147993808487207233004235013400016406600181299740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558085296782709336641/100000000000000000000)
  centralHi := (279042648391354668321/50000000000000000000)
  directionLo := (56031319105739882477/10000000000000000000)
  directionHi := (560313191057398824771/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree127.table
  base := (7127333227338928103507904488313376575383/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-46707983097694299698884857523359220800000000000000)
      constant := (1652713091680328691762626664021446680925780646312640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree127.table
  base := (71273332182567844602482719255989877874589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-35039852189659071976030429954338435600000000000000)
      constant := (1240150669655763137072676937350967001891844985092984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56031319105739882477/10000000000000000000)
  centralHi := (560313191057398824771/100000000000000000000)
  directionLo := (22501290475376934751/4000000000000000000)
  directionHi := (70316532735552921097/12500000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree128.table
  base := (72885070083424547260609494858426069940347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-47063504725083599197499565656442513600000000000000)
      constant := (1678232706241886859436470971407567738379556270036576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree128.table
  base := (72885070001570648965868284969874793813131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-35306563212298592640951042052669165200000000000000)
      constant := (1259299954330328129374858218530772590141618145099336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell136.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22501290475376934751/4000000000000000000)
  centralHi := (70316532735552921097/12500000000000000000)
  directionLo := (564742613275008524481/100000000000000000000)
  directionHi := (282371306637504262241/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree129.table
  base := (74513160157756874055935799869075857506843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14494297059)
      previous := (0)
      next := (12919790125)
      square := (336211575124162727556220702991846400000000000000)
      linear := (-47419026352472898696114273789525806400000000000000)
      constant := (1703947700798675910907963075912161277715738097166944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree129.table
  base := (149026320167978943050756402554137844333277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1699220280000000000000000000000000000000000000000
      center := (10873568563)
      previous := (0)
      next := (9686996825)
      square := (252158681343122045667165527243884800000000000000)
      linear := (-35573274234938113305871654150999894800000000000000)
      constant := (1278595847821805243017424093397456577200658735725756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell136.Kernel129
