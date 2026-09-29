import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell004.Parameters
import ForestUnimodality.BinomialMassData.Q39_140.Batch000_049
import ForestUnimodality.BinomialMassData.Q39_140.Batch050_099
import ForestUnimodality.BinomialMassData.Q39_140.Batch100_149
import ForestUnimodality.BinomialMassData.Q2_7.Batch000_049
import ForestUnimodality.BinomialMassData.Q2_7.Batch050_099
import ForestUnimodality.BinomialMassData.Q2_7.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree000.table
  base := (509549761028499624936571877/100000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (13500327947348318008424783200000000000000)
      linear := (19658344853154005593687259300000000000000)
      constant := (3566848327199497374556003139000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree000.table
  base := (509549761028499624936571877/100000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (45)
      previous := (18)
      next := (0)
      square := (675016397367415900421239160000000000000)
      linear := (982917242657700279684362965000000000000)
      constant := (178342416359974868727800156950000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree001.table
  base := (148120668905972480013627293057/40000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (84957134977419598922954160620000000000000)
      constant := (18113781739520805916365515420721500000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree001.table
  base := (146712682551941899982785805483/40000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (4180355109134238356105584115000000000000)
      constant := (897035069800967260206863612173375000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (7134853930393894497/25000000000000000000)
  directionHi := (28539415721575577989/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree002.table
  base := (5364123066176717133182048991725944132653/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (32305855982761158690097506140000000000000)
      constant := (13094768251216966056896088425954563124999850) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree002.table
  base := (26309707330126317889624681673472133928571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (2960579039329149508841254950000000000000)
      constant := (1284398110480036161327488734440134562499979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7134853930393894497/25000000000000000000)
  centralHi := (28539415721575577989/100000000000000000000)
  directionLo := (403608287756561131/1000000000000000000)
  directionHi := (40360828775656113101/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree003.table
  base := (193092157816180622118274430231476073627/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-20345423011897281542759148340000000000000)
      constant := (9412516554627346381507136206303327607723000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree003.table
  base := (468804496511313698774460464437172604503/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-1219776069805088847264329165000000000000)
      constant := (457002416025887933465888593038429152412940) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (403608287756561131/1000000000000000000)
  centralHi := (40360828775656113101/100000000000000000000)
  directionLo := (2471585902404944637/5000000000000000000)
  directionHi := (49431718048098892741/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree004.table
  base := (13758379443103136054950484152738918567493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-72996702006555721775615802820000000000000)
      constant := (6705607973311174232956771442286070098071570) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree004.table
  base := (1652189583394219028440152024332665676177/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-3919841659274752448949285805000000000000)
      constant := (322137398894221701283503365369202472530692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2471585902404944637/5000000000000000000)
  centralHi := (49431718048098892741/100000000000000000000)
  directionLo := (7134853930393894497/12500000000000000000)
  directionHi := (57078831443151155977/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree005.table
  base := (1204136446774409957596281700060810562843/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-125647981001214162008472457300000000000000)
      constant := (4711885284108121119335527907913377406344560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree005.table
  base := (2284909876449595888062414691547599500343/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-6619907248744416050634242445000000000000)
      constant := (223735086856446478525004998121664751033614) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7134853930393894497/12500000000000000000)
  centralHi := (57078831443151155977/100000000000000000000)
  directionLo := (63816073591569203843/100000000000000000000)
  directionHi := (15954018397892300961/25000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree006.table
  base := (328369172700555729184961492646504918477/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-178299259995872602241329111780000000000000)
      constant := (3252023813785331602305520061589748201074600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree006.table
  base := (1226803959425607917117599035938088339597/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-18639945676428159304638398170000000000000)
      constant := (304749059441462815741575178084831643201265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63816073591569203843/100000000000000000000)
  centralHi := (15954018397892300961/25000000000000000000)
  directionLo := (8738375759378043961/12500000000000000000)
  directionHi := (69907006075024351689/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree007.table
  base := (4266132259903601815594072440474244470133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (13500327947348318008424783200000000000000)
      linear := (-32992934141504434639169395180000000000000)
      constant := (311630482749393795410930153316197112909310) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree007.table
  base := (3894912516050048399674513083016947157713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (90)
      previous := (36)
      next := (0)
      square := (1350032794734831800842478320000000000000)
      linear := (-3434296693623926644001187350000000000000)
      constant := (28732849820658864882354053001118630103991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8738375759378043961/12500000000000000000)
  centralHi := (69907006075024351689/100000000000000000000)
  directionLo := (75508196562375974161/100000000000000000000)
  directionHi := (37754098281187987081/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree008.table
  base := (2519999420412099842041989161881801294139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-283601817985189482707042420740000000000000)
      constant := (1397478080473681673986232764178082634128110) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree008.table
  base := (2207304728161454907442953776414199470933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-29440208034306813711378224730000000000000)
      constant := (126077207836595873088472898724295774075717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75508196562375974161/100000000000000000000)
  centralHi := (37754098281187987081/50000000000000000000)
  directionLo := (403608287756561131/500000000000000000)
  directionHi := (80721657551312226201/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree009.table
  base := (1180545511227750948692612358240614264323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-336253096979847922939899075220000000000000)
      constant := (827482599557766640603004981616900989518270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree009.table
  base := (920092379821419948270868417599744448271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-34840339213246140914748138010000000000000)
      constant := (72186738089013153607058767962387477965279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (403608287756561131/500000000000000000)
  centralHi := (80721657551312226201/100000000000000000000)
  directionLo := (21404561791181683491/25000000000000000000)
  directionHi := (17123649432945346793/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree010.table
  base := (13980102345298891583874742136021641301/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-388904375974506363172755729700000000000000)
      constant := (418521877138204020070302367516506042374900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree010.table
  base := (-9448717413602739346686367227692935987/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-20120235196092734059059025645000000000000)
      constant := (17062072097632194661290164723372184546548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21404561791181683491/25000000000000000000)
  centralHi := (17123649432945346793/20000000000000000000)
  directionLo := (22562389192649169507/25000000000000000000)
  directionHi := (90249556770596678029/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree011.table
  base := (-340409642925100928556459103501884532863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-441555654969164803405612384180000000000000)
      constant := (132089144175366168097401768337153157794260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree011.table
  base := (-34329423939474091762329961340814370019/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-45640601571124795321487964570000000000000)
      constant := (8043221661728081228999470737502396726725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22562389192649169507/25000000000000000000)
  centralHi := (90249556770596678029/100000000000000000000)
  directionLo := (18930906736887240771/20000000000000000000)
  directionHi := (5915908355277262741/6250000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree012.table
  base := (-669283427608167998728477097736497786163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-494206933963823243638469038660000000000000)
      constant := (-59868804212659082690035953545767830439740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree012.table
  base := (-371125277186232014881035947646995912883/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-25520366375032061262428938925000000000000)
      constant := (-4416084576088178650389983149405599462534) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18930906736887240771/20000000000000000000)
  centralHi := (5915908355277262741/6250000000000000000)
  directionLo := (2471585902404944637/2500000000000000000)
  directionHi := (98863436096197785481/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree013.table
  base := (-468800198516552664470545293834508984781/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-546858212958481683871325693140000000000000)
      constant := (-177813931642062337109532907464637610170760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree013.table
  base := (-199533532034968063171511869021621717069/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-28220431964501724864113895565000000000000)
      constant := (-9254265854756932936705606120297320681905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2471585902404944637/2500000000000000000)
  centralHi := (98863436096197785481/100000000000000000000)
  directionLo := (2058006535118477071/2000000000000000000)
  directionHi := (102900326755923853551/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree014.table
  base := (-2321225330234742099721394158785254403949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (13500327947348318008424783200000000000000)
      linear := (-85644213136162874872026049660000000000000)
      constant := (-33813329964564651887736949912967808276430) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree014.table
  base := (-484076962393232314111226149258692013941/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (90)
      previous := (36)
      next := (0)
      square := (1350032794734831800842478320000000000000)
      linear := (-8834427872563253847371100630000000000000)
      constant := (-3205506909267424417888165824054220487935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2058006535118477071/2000000000000000000)
  centralHi := (102900326755923853551/100000000000000000000)
  directionLo := (106784715648845615883/100000000000000000000)
  directionHi := (26696178912211403971/25000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree015.table
  base := (-2698963609854650173710617456667724025429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-652160770947798564337039002100000000000000)
      constant := (-247445280147362487864565091642184772460210) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree015.table
  base := (-34764471122542074414810670475335452761/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-33620563143441052067483808845000000000000)
      constant := (-10838058161245715617971911081657487411560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106784715648845615883/100000000000000000000)
  centralHi := (26696178912211403971/25000000000000000000)
  directionLo := (55266340900076171571/50000000000000000000)
  directionHi := (110532681800152343143/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree016.table
  base := (-1512393836308815025888582362218502107897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-704812049942457004569895656580000000000000)
      constant := (-218092142277222745305135925390132065739060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree016.table
  base := (-1546648454680262210592564436376841937323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-36320628732910715669168765485000000000000)
      constant := (-8493870200917274121599715142465254928827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55266340900076171571/50000000000000000000)
  centralHi := (110532681800152343143/100000000000000000000)
  directionLo := (7134853930393894497/6250000000000000000)
  directionHi := (114157662886302311953/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree017.table
  base := (-82768415631065093910552493335381567017/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-757463328937115444802752311060000000000000)
      constant := (-154533058433805126561392398582478713533200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree017.table
  base := (-842053528665023096208500544838009165193/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-39020694322380379270853722125000000000000)
      constant := (-4466295580000818525279612924124898188914) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7134853930393894497/6250000000000000000)
  centralHi := (114157662886302311953/100000000000000000000)
  directionLo := (117671025513469370671/100000000000000000000)
  directionHi := (7354439094591835667/6250000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree018.table
  base := (-1782845626061416332040115774374759646671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-810114607931773885035608965540000000000000)
      constant := (-61119612969807706086390953141264453737580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree018.table
  base := (-3614264345041319016413265390101375609311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-83441519823700085745077357530000000000000)
      constant := (2079934475384092900168991365032595143761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117671025513469370671/100000000000000000000)
  centralHi := (7354439094591835667/6250000000000000000)
  directionLo := (1210824863269683393/1000000000000000000)
  directionHi := (121082486326968339301/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree019.table
  base := (-3796227020782131822022327998264554399699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-862765886926432325268465620020000000000000)
      constant := (58926215028100142957192175299368344147490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree019.table
  base := (-1918795533538879306233136473671680212999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-44420825501319706474223635405000000000000)
      constant := (7874403321109240539180426840087669563049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1210824863269683393/1000000000000000000)
  centralHi := (121082486326968339301/100000000000000000000)
  directionLo := (7775026814877742279/6250000000000000000)
  directionHi := (24880085807608775293/20000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree020.table
  base := (-4007233878986755533788738483080199688521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-915417165921090765501322274500000000000000)
      constant := (203208351154453811834585780190702152624710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree020.table
  base := (-4042734449158412116106256955979363437117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-94241782181578740151817184090000000000000)
      constant := (31851557089440481271467987957011191581267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7775026814877742279/6250000000000000000)
  centralHi := (24880085807608775293/20000000000000000000)
  directionLo := (127632147183138407687/100000000000000000000)
  directionHi := (15954018397892300961/12500000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree021.table
  base := (-4202366912098072102887006087250745723087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (13500327947348318008424783200000000000000)
      linear := (-138295492130821315104882704140000000000000)
      constant := (52847971940311833118156250049447799383910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree021.table
  base := (-4233069568645229273811861350937132844721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (90)
      previous := (36)
      next := (0)
      square := (1350032794734831800842478320000000000000)
      linear := (-14234559051502581050741013910000000000000)
      constant := (7174686718044936557433834483440070086953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127632147183138407687/100000000000000000000)
  centralHi := (15954018397892300961/12500000000000000000)
  directionLo := (130784032833932830383/100000000000000000000)
  directionHi := (8174002052120801899/6250000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree022.table
  base := (-4384374297027745271744520392601839633973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-1020719723910407645967035583460000000000000)
      constant := (557761965624571969145295190671098579353230) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree022.table
  base := (-4411122418861680425521947970255373569903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-105042044539457394558557010650000000000000)
      constant := (70738782779990658313063183897486695074753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130784032833932830383/100000000000000000000)
  centralHi := (8174002052120801899/6250000000000000000)
  directionLo := (1673271565957883071/1250000000000000000)
  directionHi := (133861725276630645681/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree023.table
  base := (-4555336211333031236439487099635617729089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-1073371002905066086199892237940000000000000)
      constant := (765667550278565687710869307919547312746390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree023.table
  base := (-457879807589316054847510094196802099943/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-55221087859198360880963461965000000000000)
      constant := (46653067811142217309928196611783485513965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1673271565957883071/1250000000000000000)
  centralHi := (133861725276630645681/100000000000000000000)
  directionLo := (17108778696807347643/12500000000000000000)
  directionHi := (27374045914891756229/20000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree024.table
  base := (-589604887071329772260165204457530694537/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-1126022281899724526432748892420000000000000)
      constant := (992875201181376978780202542710479677414960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree024.table
  base := (-4737545692570568796718244900108777424611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-115842306897336048965296837210000000000000)
      constant := (117853857064481826274117162294669906194061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17108778696807347643/12500000000000000000)
  centralHi := (27374045914891756229/20000000000000000000)
  directionLo := (8738375759378043961/6250000000000000000)
  directionHi := (139814012150048703377/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree025.table
  base := (-974020593062894215569657126888446292047/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-1178673560894382966665605546900000000000000)
      constant := (1238787112171792401575946694498306584484850) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree025.table
  base := (-4888478031710014387350632058154242498227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-121242438076275376168666750490000000000000)
      constant := (144327421728593481637982132650442117586877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8738375759378043961/6250000000000000000)
  centralHi := (139814012150048703377/100000000000000000000)
  directionLo := (7134853930393894497/5000000000000000000)
  directionHi := (142697078607877889941/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree026.table
  base := (-627009322383402695295533732725618193481/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-1231324839889041406898462201380000000000000)
      constant := (1502939370113493059052395288029576681554480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree026.table
  base := (-5032458259467280687563707990018863026343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-126642569255214703372036663770000000000000)
      constant := (172684534472986015719070471169075711709193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7134853930393894497/5000000000000000000)
  centralHi := (142697078607877889941/100000000000000000000)
  directionLo := (145523037670850579963/100000000000000000000)
  directionHi := (36380759417712644991/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree027.table
  base := (-644436975098112501985688540998539724849/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-1283976118883699847131318855860000000000000)
      constant := (1784968462158033862923993658286724278591920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree027.table
  base := (-2585081568835831086374591023792833855281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-66021350217077015287703288525000000000000)
      constant := (101446016984011999611594209804151141091231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145523037670850579963/100000000000000000000)
  centralHi := (36380759417712644991/25000000000000000000)
  directionLo := (148295154144296678221/100000000000000000000)
  directionHi := (74147577072148339111/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree028.table
  base := (-2644476936072497137363501269456660600401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (13500327947348318008424783200000000000000)
      linear := (-190946771125479755337739358620000000000000)
      constant := (297798091411920824770913009624067515943860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree028.table
  base := (-2651064591551906730407963180788960496313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (45)
      previous := (18)
      next := (0)
      square := (675016397367415900421239160000000000000)
      linear := (-9817345115220954127055463595000000000000)
      constant := (16780259349389668276628660254477276525809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148295154144296678221/100000000000000000000)
  centralHi := (74147577072148339111/50000000000000000000)
  directionLo := (151016393124751948323/100000000000000000000)
  directionHi := (37754098281187987081/25000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree029.table
  base := (-1083383702969288937751775872480816998637/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-1389278676873016727597032164820000000000000)
      constant := (2401563739657248019033225350040998353339350) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree029.table
  base := (-1357196629057941913192683585802314714941/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-71421481396016342491073201805000000000000)
      constant := (134379124670173231859288032941373157935782) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151016393124751948323/100000000000000000000)
  centralHi := (37754098281187987081/25000000000000000000)
  directionLo := (38422364290002494909/25000000000000000000)
  directionHi := (153689457160009979637/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree030.table
  base := (-5539769413558356905722333822374034184859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-1441929955867675167829888819300000000000000)
      constant := (2735713715991578832441310944586723249419090) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree030.table
  base := (-5550483796985078219975883561017348566301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-148243093970972012185516316890000000000000)
      constant := (304378804978149202663761285710149920251251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38422364290002494909/25000000000000000000)
  centralHi := (153689457160009979637/100000000000000000000)
  directionLo := (9769801105452825853/6250000000000000000)
  directionHi := (156316817687245213649/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree031.table
  base := (-5657816665391035785985843318412823707281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-1494581234862333608062745473780000000000000)
      constant := (3086884621302388832040093925206716383432310) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree031.table
  base := (-1416876673426303306591721558596239630237/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-76821612574955669694443115085000000000000)
      constant := (170885650028065818787758402147568516236774) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9769801105452825853/6250000000000000000)
  centralHi := (156316817687245213649/100000000000000000000)
  directionLo := (31780148358115871661/20000000000000000000)
  directionHi := (79450370895289679153/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree032.table
  base := (-721414509418090549371117899235600487063/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-1547232513856992048295602128260000000000000)
      constant := (3454951111139558915774001973652446090713040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree032.table
  base := (-5780091647983547589953482260716344097543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-159043356328850666592256143450000000000000)
      constant := (380924148936316397471365366664899139220393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31780148358115871661/20000000000000000000)
  centralHi := (79450370895289679153/50000000000000000000)
  directionLo := (403608287756561131/250000000000000000)
  directionHi := (161443315102624452401/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree033.table
  base := (-294024033274518994033748790258559153197/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-1599883792851650488528458782740000000000000)
      constant := (3839808804688320081121397335297120298669400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree033.table
  base := (-2944218103507576187316015767609753598049/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-82221743753894996897813028365000000000000)
      constant := (210913835903072500110192668977122073695599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (403608287756561131/250000000000000000)
  centralHi := (161443315102624452401/100000000000000000000)
  directionLo := (16394646150818322517/10000000000000000000)
  directionHi := (163946461508183225171/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree034.table
  base := (-2992744697163055875228380944256163384561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-1652535071846308928761315437220000000000000)
      constant := (4241370012284598669479397849382959883130220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree034.table
  base := (-1198541368413616927619428043941747083603/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-169843618686729320998995970010000000000000)
      constant := (464473711573482649995541016234271964517265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16394646150818322517/10000000000000000000)
  centralHi := (163946461508183225171/100000000000000000000)
  directionLo := (166411960179498874681/100000000000000000000)
  directionHi := (83205980089749437341/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree035.table
  base := (-6086493813198257712116916261560790483693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (13500327947348318008424783200000000000000)
      linear := (-243598050120138195570596013100000000000000)
      constant := (665651496252669886289246036465744666141490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree035.table
  base := (-6093044917744242875532947553994986285489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (90)
      previous := (36)
      next := (0)
      square := (1350032794734831800842478320000000000000)
      linear := (-25034821409381235457480840470000000000000)
      constant := (72693620196119474361829939822035096001577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (166411960179498874681/100000000000000000000)
  centralHi := (83205980089749437341/50000000000000000000)
  directionLo := (168841460371888617493/100000000000000000000)
  directionHi := (84420730185944308747/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree036.table
  base := (-1545905797721702833069984959485287420981/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-1757837629835625809227028746180000000000000)
      constant := (5094316847438394837111365105252836654877240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree036.table
  base := (-1547392823485774470452223709444285739079/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-90321940522303987702867898285000000000000)
      constant := (277483319534565971441794200914459997570258) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (168841460371888617493/100000000000000000000)
  centralHi := (84420730185944308747/50000000000000000000)
  directionLo := (21404561791181683491/12500000000000000000)
  directionHi := (171236494329453467929/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree037.table
  base := (-392311780946924465412747327776980910073/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-1810488908830284249459885400660000000000000)
      constant := (5545584759091796339266845332239469665027680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree037.table
  base := (-3141194955390761936611307395186040394701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-93022006111773651304552854925000000000000)
      constant := (301401255798321340224646741105884020659651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21404561791181683491/12500000000000000000)
  centralHi := (171236494329453467929/100000000000000000000)
  directionLo := (173598488587803854029/100000000000000000000)
  directionHi := (17359848858780385403/10000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree038.table
  base := (-1273337103303086545457303543775022647629/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-1863140187824942689692742055140000000000000)
      constant := (6013317271371528721114363809677194513308950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree038.table
  base := (-637159061178208376479974085934826586983/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-95722071701243314906237811565000000000000)
      constant := (326179278311381475196834390485967486189165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173598488587803854029/100000000000000000000)
  centralHi := (17359848858780385403/10000000000000000000)
  directionLo := (175928773910633448189/100000000000000000000)
  directionHi := (17592877391063344819/10000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree039.table
  base := (-806599668026414502993736295315906502719/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-1915791466819601129925598709620000000000000)
      constant := (6497473670554607366339008677950646509341520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree039.table
  base := (-201789106002855732060655895886682414323/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-98422137290712978507922768205000000000000)
      constant := (351815476192654532558039616274840987170768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (175928773910633448189/100000000000000000000)
  centralHi := (17592877391063344819/10000000000000000000)
  directionLo := (4455714851417481549/2500000000000000000)
  directionHi := (178228594056699261961/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree040.table
  base := (-3267698174614256031793841379973895503727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-1968442745814259570158455364100000000000000)
      constant := (6998018494855897618713912220625582406347540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree040.table
  base := (-6539440208916793682083989274024595414443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-202244405760365284219215449690000000000000)
      constant := (756616368981119854170080915172794824692293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4455714851417481549/2500000000000000000)
  centralHi := (178228594056699261961/100000000000000000000)
  directionLo := (22562389192649169507/12500000000000000000)
  directionHi := (180499113541193356057/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree041.table
  base := (-264581831573311127548724190403919619041/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-2021094024808918010391312018580000000000000)
      constant := (7514920747970178380405151611710984666747750) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree041.table
  base := (-3309108227726060527738329802039679700327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-103822268469652305711292681485000000000000)
      constant := (405655948071849398982762949690055694683977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22562389192649169507/12500000000000000000)
  centralHi := (180499113541193356057/100000000000000000000)
  directionLo := (182741424528992675851/100000000000000000000)
  directionHi := (45685356132248168963/25000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree042.table
  base := (-836287640193821900713515870841267499313/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (13500327947348318008424783200000000000000)
      linear := (-296249329114796635803452667580000000000000)
      constant := (1149736179422069122327558750766890200384720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree042.table
  base := (-6693632173479038513447626277815215487401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (90)
      previous := (36)
      next := (0)
      square := (1350032794734831800842478320000000000000)
      linear := (-30434952588320562660850753750000000000000)
      constant := (123959283403677703014758782975293491588193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (182741424528992675851/100000000000000000000)
  centralHi := (45685356132248168963/25000000000000000000)
  directionLo := (92478276487797988819/50000000000000000000)
  directionHi := (184956552975595977639/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree043.table
  base := (-3381355543062277575602647333168202119061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-2126396582798234890857025327540000000000000)
      constant := (8597692136089914548419893961216161923320220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree043.table
  base := (-6765733060836055563097275556681738405691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-218444799297183265829325189530000000000000)
      constant := (925823392833168257735518732702594818121141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92478276487797988819/50000000000000000000)
  centralHi := (184956552975595977639/100000000000000000000)
  directionLo := (93572732056864937621/50000000000000000000)
  directionHi := (187145464113729875243/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree044.table
  base := (-6831818610138254159980434978589448872511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-2179047861792893331089881982020000000000000)
      constant := (9163516354105537750748394440615170052469610) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree044.table
  base := (-6834559316067779255100755495503796770653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-223844930476122593032695102810000000000000)
      constant := (985635153437286062379065400320313958238003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93572732056864937621/50000000000000000000)
  centralHi := (187145464113729875243/100000000000000000000)
  directionLo := (18930906736887240771/10000000000000000000)
  directionHi := (189309067368872407711/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree045.table
  base := (-6897661567360315797313609753533400143163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-2231699140787551771322738636500000000000000)
      constant := (9745607351854718116291182387043633929850130) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree045.table
  base := (-431259147024117789121456363582088196393/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-114622530827530960118032508045000000000000)
      constant := (523574265195362629123087466625821427013944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18930906736887240771/10000000000000000000)
  centralHi := (189309067368872407711/100000000000000000000)
  directionLo := (191448220774707611531/100000000000000000000)
  directionHi := (47862055193676902883/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree046.table
  base := (-1740068355560286828760296742900406914219/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-2284350419782210211555595290980000000000000)
      constant := (10343948731756756091648437490089202448130760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree046.table
  base := (-6962525405569260279073469367400845462023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-234645192834001247439434929370000000000000)
      constant := (1110361993140320303767868144077358572360873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191448220774707611531/100000000000000000000)
  centralHi := (47862055193676902883/25000000000000000000)
  directionLo := (96781867474659351043/50000000000000000000)
  directionHi := (193563734949318702087/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree047.table
  base := (-3509841889796210286655715303278130585459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-2337001698776868651788451945460000000000000)
      constant := (10958525987453932465347510402608432026250180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree047.table
  base := (-3510862027434837355666620101459833651897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-120022662006470287321402421325000000000000)
      constant := (587637095151367271299443955998468151057047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96781867474659351043/50000000000000000000)
  centralHi := (193563734949318702087/100000000000000000000)
  directionLo := (97828188342188747743/50000000000000000000)
  directionHi := (195656376684377495487/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree048.table
  base := (-7075918856699138743838317031944016460921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-2389652977771527092021308599940000000000000)
      constant := (11589326272476595683248552701563431934148710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree048.table
  base := (-7077766671841718977086302062843927692931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-245445455191879901846174755930000000000000)
      constant := (1241883927671793013075413537800647543046381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97828188342188747743/50000000000000000000)
  centralHi := (195656376684377495487/100000000000000000000)
  directionLo := (197726872192395570961/100000000000000000000)
  directionHi := (98863436096197785481/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree049.table
  base := (-1782250472755908374325614101789718772681/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (13500327947348318008424783200000000000000)
      linear := (-348900608109455076036309322060000000000000)
      constant := (1748048314352600460959723629835878743649320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree049.table
  base := (-3565337404449941915084448446440516333677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (45)
      previous := (18)
      next := (0)
      square := (675016397367415900421239160000000000000)
      linear := (-17917541883629944932110333515000000000000)
      constant := (93585010655656119161390654724916385664261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (197726872192395570961/100000000000000000000)
  centralHi := (98863436096197785481/50000000000000000000)
  directionLo := (49943977512757261479/25000000000000000000)
  directionHi := (199775910051029045917/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree050.table
  base := (-179473837348666270617720928248669229917/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-2494955535760843972487021908900000000000000)
      constant := (12899551671852189560163604209576083093626800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree050.table
  base := (-3590233768522793157764975803705521101921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-128122858774879278126457291245000000000000)
      constant := (690095960172921536474278689118429466005871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49943977512757261479/25000000000000000000)
  centralHi := (199775910051029045917/100000000000000000000)
  directionLo := (201804143878280565501/100000000000000000000)
  directionHi := (100902071939140282751/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree051.table
  base := (-225805998716361245521428913476397649353/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-2547606814755502412719878563380000000000000)
      constant := (13578957722835423809577318748579084858144960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree051.table
  base := (-722716174040316966090631675307533504121/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-130822924364348941728142247885000000000000)
      constant := (725944206924836204491786248639654291490355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201804143878280565501/100000000000000000000)
  centralHi := (100902071939140282751/50000000000000000000)
  directionLo := (101906097384031293681/50000000000000000000)
  directionHi := (203812194768062587363/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree052.table
  base := (-7269533530846416166935487619931087817837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-2600258093750160852952735217860000000000000)
      constant := (14274548393420798743845049240509766969259870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree052.table
  base := (-7270772373811627205082796856463167956519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-267045979907637210659654409050000000000000)
      constant := (1525278896903563002764059101473304770130569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101906097384031293681/50000000000000000000)
  centralHi := (203812194768062587363/100000000000000000000)
  directionLo := (205800653511847707101/100000000000000000000)
  directionHi := (102900326755923853551/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree053.table
  base := (-3655096321086386557663209551361768454537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-2652909372744819293185591872340000000000000)
      constant := (14986316611704113216631331230076466914553740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree053.table
  base := (-913914086079104431700250029225037692651/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-136223055543288268931512161165000000000000)
      constant := (800181360095391452759214691661892612240404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205800653511847707101/100000000000000000000)
  centralHi := (102900326755923853551/50000000000000000000)
  directionLo := (25971260328616282941/12500000000000000000)
  directionHi := (207770082628930263529/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree054.table
  base := (-3673891060210029066505301216207493586931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-2705560651739477733418448526820000000000000)
      constant := (15714256092201827786671644168410656284807620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree054.table
  base := (-918599303885089132369686643330314578487/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-138923121132757932533197117805000000000000)
      constant := (838569654073425051637249298007258342616548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25971260328616282941/12500000000000000000)
  centralHi := (207770082628930263529/100000000000000000000)
  directionLo := (26215127278134131883/12500000000000000000)
  directionHi := (41944203645014611013/20000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree055.table
  base := (-3691156685432038206648175466724885672083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-2758211930734136173651305181300000000000000)
      constant := (16458361246328797909244914526534612041358660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree055.table
  base := (-7383228016692819963622752710657443315473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-283246373444455192269764148890000000000000)
      constant := (1755608150410424158851066360877785277541823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26215127278134131883/12500000000000000000)
  centralHi := (41944203645014611013/20000000000000000000)
  directionLo := (105826985848471489697/50000000000000000000)
  directionHi := (42330794339388595879/20000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree056.table
  base := (-7413796537673149040962683070596559082247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (13500327947348318008424783200000000000000)
      linear := (-401551887104113516269165976540000000000000)
      constant := (2459803871920363750401346179530240864242710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree056.table
  base := (-1853655671003806194619682896889488268569/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (45)
      previous := (18)
      next := (0)
      square := (675016397367415900421239160000000000000)
      linear := (-20617607473099608533795290155000000000000)
      constant := (131126342449481979308211856963547164240034) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105826985848471489697/50000000000000000000)
  centralHi := (42330794339388595879/20000000000000000000)
  directionLo := (213569431297691231767/100000000000000000000)
  directionHi := (26696178912211403971/12500000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree057.table
  base := (-1488448129243909510951976894826330036007/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-2863514488723453054117018490260000000000000)
      constant := (17995049241110659763377530400106491411782850) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree057.table
  base := (-372149331506126655140191402076556938933/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-147023317901166923338251987725000000000000)
      constant := (958810419068582541650777995452487099922830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213569431297691231767/100000000000000000000)
  centralHi := (26696178912211403971/12500000000000000000)
  directionLo := (43093572715451741863/20000000000000000000)
  directionHi := (53866965894314677329/25000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree058.table
  base := (-58341044757113266569915587146483543709/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-2916165767718111494349875144740000000000000)
      constant := (18787623723453597619481228351478552138571520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree058.table
  base := (-7468327130225151738722139695449912551161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-299446766981273173879873888730000000000000)
      constant := (2001163925458366344506755557602954284993111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43093572715451741863/20000000000000000000)
  centralHi := (53866965894314677329/25000000000000000000)
  directionLo := (27168714338680611597/12500000000000000000)
  directionHi := (217349714709444892777/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree059.table
  base := (-1872510734138026200513251132209570718143/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-2968817046712769934582731799220000000000000)
      constant := (19596347046576368830484546296798241392439720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree059.table
  base := (-3745325321654117726699409789933699700353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-152423449080106250541621901005000000000000)
      constant := (1043198869883039455169736099543248714682703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27168714338680611597/12500000000000000000)
  centralHi := (217349714709444892777/100000000000000000000)
  directionLo := (21921541171643475683/10000000000000000000)
  directionHi := (219215411716434756831/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree060.table
  base := (-7509414636986056976318907418928929207547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-3021468325707428374815588453700000000000000)
      constant := (20421216090236545601046162773024824688301970) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree060.table
  base := (-375498145274428281291599756717262936709/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-155123514669575914143306857645000000000000)
      constant := (1086660999995290246614398835408541161012590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21921541171643475683/10000000000000000000)
  centralHi := (219215411716434756831/100000000000000000000)
  directionLo := (55266340900076171571/25000000000000000000)
  directionHi := (44213072720060937257/20000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree061.table
  base := (-940721812813696368108578791420636296063/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-3074119604702086815048445108180000000000000)
      constant := (21262228075008491943616431792050105719433040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree061.table
  base := (-1881567253139286318179052079517434609361/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-157823580259045577744991814285000000000000)
      constant := (1130968228219055972678349708397291408282622) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55266340900076171571/25000000000000000000)
  centralHi := (44213072720060937257/20000000000000000000)
  directionLo := (222899962390000935139/100000000000000000000)
  directionHi := (11144998119500046757/5000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree062.table
  base := (-1884781896848750414604431701969595570149/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-3126770883696745255281301762660000000000000)
      constant := (22119380524298753932344732118425592682507960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree062.table
  base := (-1884893373247280114142359719699369135033/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-160523645848515241346676770925000000000000)
      constant := (1176120443606695554829898214689461824766766) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222899962390000935139/100000000000000000000)
  centralHi := (11144998119500046757/5000000000000000000)
  directionLo := (44943916822276514473/20000000000000000000)
  directionHi := (112359792055691286183/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree063.table
  base := (-7549478396660282992830678356955687201271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (13500327947348318008424783200000000000000)
      linear := (-454203166098771956502022631020000000000000)
      constant := (3284667318664077709722495401856101895911030) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree063.table
  base := (-7549880372542985018008265219823217836537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (90)
      previous := (36)
      next := (0)
      square := (1350032794734831800842478320000000000000)
      linear := (-46635346125138544270960493590000000000000)
      constant := (349176442150607398278268052401237475144241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44943916822276514473/20000000000000000000)
  centralHi := (112359792055691286183/50000000000000000000)
  directionLo := (45304917937425584497/20000000000000000000)
  directionHi := (113262294843563961243/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree064.table
  base := (-7556830947099643877615003111827088522801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-3232073441686062135747015071620000000000000)
      constant := (23882098225828689875295954990468726623827510) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree064.table
  base := (-3778596615716686920412777020919585888301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-165923777027454568550046684205000000000000)
      constant := (1268959452265088435457544380374940291473251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45304917937425584497/20000000000000000000)
  centralHi := (113262294843563961243/50000000000000000000)
  directionLo := (45663065154520924781/20000000000000000000)
  directionHi := (114157662886302311953/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree065.table
  base := (-7561188821461852625397163990472189796907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-3284724720680720575979871726100000000000000)
      constant := (24787659754292295180873226821043626999515570) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree065.table
  base := (-7561515254942518345310340903950817275233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-337247685233848464303463281690000000000000)
      constant := (2633292159562337018967270868806409953513583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45663065154520924781/20000000000000000000)
  centralHi := (114157662886302311953/50000000000000000000)
  directionLo := (57523031383296536761/25000000000000000000)
  directionHi := (46018425106637229409/20000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree066.table
  base := (-3781277608278678885630668292961448140607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-3337375999675379016212728380580000000000000)
      constant := (25709354249602240102598037264131780822205140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree066.table
  base := (-1512569855646351485673657123927673676083/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-342647816412787791506833194970000000000000)
      constant := (2730354721227826626156045360117719949359665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57523031383296536761/25000000000000000000)
  centralHi := (46018425106637229409/20000000000000000000)
  directionLo := (231855309367951304073/100000000000000000000)
  directionHi := (115927654683975652037/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree067.table
  base := (-3780466492991778700527651586372796652491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-3390027278670037456445585035060000000000000)
      constant := (26647180313495799578404973005195659280558820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree067.table
  base := (-7561197826024043187371236402817952374397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-348047947591727118710203108250000000000000)
      constant := (2829106465815221039710191672201920333654547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231855309367951304073/100000000000000000000)
  centralHi := (115927654683975652037/50000000000000000000)
  directionLo := (233605185584218834159/100000000000000000000)
  directionHi := (2920064819802735427/1250000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree068.table
  base := (-472270292379810556452276986019286665627/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-3442678557664695896678441689540000000000000)
      constant := (27601136697288080087949923711804792541484320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree068.table
  base := (-7556563147749250027262040481903232184369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-353448078770666445913573021530000000000000)
      constant := (2929547283102456413787510290866741622965919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233605185584218834159/100000000000000000000)
  centralHi := (2920064819802735427/1250000000000000000)
  directionLo := (235342051026938741343/100000000000000000000)
  directionHi := (7354439094591835667/3125000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree069.table
  base := (-1887183142407648976431735563461394554277/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-3495329836659354336911298344020000000000000)
      constant := (28571222285350509853551001653914666673617080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree069.table
  base := (-377447362433735675942715509687272200971/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-179424104974802886558471467405000000000000)
      constant := (1515838537415716652709067105803236621524210) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235342051026938741343/100000000000000000000)
  centralHi := (7354439094591835667/3125000000000000000)
  directionLo := (118533095833289482117/50000000000000000000)
  directionHi := (47413238333315792847/20000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree070.table
  base := (-3769079347926451937757319736964068882129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (13500327947348318008424783200000000000000)
      linear := (-506854445093430396734879285500000000000000)
      constant := (4222490868632991542340597492275030356501940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree070.table
  base := (-7538351917482476674521841525209904770713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (90)
      previous := (36)
      next := (0)
      square := (1350032794734831800842478320000000000000)
      linear := (-52035477304077871474330406870000000000000)
      constant := (447927964765247372427963918723530666605009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118533095833289482117/50000000000000000000)
  centralHi := (47413238333315792847/20000000000000000000)
  directionLo := (238777883148804359309/100000000000000000000)
  directionHi := (23877788314880435931/10000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree071.table
  base := (-7524604876990359040711050241290282180659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-3600632394648671217377011652980000000000000)
      constant := (30559777190608604464674817953516761731477090) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree071.table
  base := (-1881194687675274631667799751707261478759/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-184824236153742213761841380685000000000000)
      constant := (1620501620224225962966214143622688375081618) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238777883148804359309/100000000000000000000)
  centralHi := (23877788314880435931/10000000000000000000)
  directionLo := (120238695654469929971/50000000000000000000)
  directionHi := (240477391308939859943/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree072.table
  base := (-1877018185496870364030559852287183418221/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-3653283673643329657609868307460000000000000)
      constant := (31578244817700686031567936398613120500286840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree072.table
  base := (-7508229174352642889567024705280093317029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-375048603486423754727052674650000000000000)
      constant := (3348199466231513135329209318881275427465579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120238695654469929971/50000000000000000000)
  centralHi := (240477391308939859943/100000000000000000000)
  directionLo := (242164972653936678601/100000000000000000000)
  directionHi := (121082486326968339301/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree073.table
  base := (-1872140937378996569427077423561454317357/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-3705934952637988097842724961940000000000000)
      constant := (32612838246958045070643087450010549537980280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree073.table
  base := (-3744352231566905264148617900805969973229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-190224367332681540965211293965000000000000)
      constant := (1728542184122888448848391292050507471311779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242164972653936678601/100000000000000000000)
  centralHi := (121082486326968339301/50000000000000000000)
  directionLo := (48768174962863153927/20000000000000000000)
  directionHi := (60960218703578942409/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree074.table
  base := (-7466079206667133354742497050122133013627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-3758586231632646538075581616420000000000000)
      constant := (33663556837905964255756385490474154823322770) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree074.table
  base := (-1866551439353353749984391201743737475793/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-192924432922151204566896250605000000000000)
      constant := (1783828945306585674369218594929113727372286) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48768174962863153927/20000000000000000000)
  centralHi := (60960218703578942409/25000000000000000000)
  directionLo := (15344083560521448421/6250000000000000000)
  directionHi := (245505336968343174737/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree075.table
  base := (-58129845981002106918122944758307551499/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-3811237510627304978308438270900000000000000)
      constant := (34730400016202043557743312148383950369982720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree075.table
  base := (-1488146815659186891083514402119199077651/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-391248997023241736337162414490000000000000)
      constant := (3679919983299577059058624681980796225975505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15344083560521448421/6250000000000000000)
  centralHi := (245505336968343174737/100000000000000000000)
  directionLo := (247158590240494463701/100000000000000000000)
  directionHi := (123579295120247231851/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree076.table
  base := (-7412188038155210535619435499270689627253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-3863888789621963418541294925380000000000000)
      constant := (35813367266397733496469958401321362082646030) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree076.table
  base := (-926536292621522614291177115828918193179/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-198324564101090531770266163885000000000000)
      constant := (1896935300730322119848664622137532034136916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247158590240494463701/100000000000000000000)
  centralHi := (123579295120247231851/50000000000000000000)
  directionLo := (7775026814877742279/3125000000000000000)
  directionHi := (248800858076087752929/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree077.table
  base := (-7380783409306110824461835424962732768149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (13500327947348318008424783200000000000000)
      linear := (-559505724088088836967735939980000000000000)
      constant := (5273208303643248308774343620545608706229570) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree077.table
  base := (-738087536655276402645974146713922811377/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (45)
      previous := (18)
      next := (0)
      square := (675016397367415900421239160000000000000)
      linear := (-28717804241508599338850160075000000000000)
      constant := (279250693204425215558214673075012701601805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7775026814877742279/3125000000000000000)
  centralHi := (248800858076087752929/100000000000000000000)
  directionLo := (25043235659380453887/10000000000000000000)
  directionHi := (250432356593804538871/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree078.table
  base := (-3673203624259717487880106239746734882309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-3969191347611280299007008234340000000000000)
      constant := (38027672177262809984975147846934199815337180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree078.table
  base := (-1836622473139398555631177833355927875911/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-203724695280029858973636077165000000000000)
      constant := (2013418628682513891153280549471119068160722) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25043235659380453887/10000000000000000000)
  centralHi := (250432356593804538871/100000000000000000000)
  directionLo := (252053294917672899217/100000000000000000000)
  directionHi := (126026647458836449609/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree079.table
  base := (-913632540037274595281654561737790206077/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-4021842626605938739239864888820000000000000)
      constant := (39159009047071472218492237693456862392178160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree079.table
  base := (-7309134582214825490345377555722537473037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-412849521738999045150642067610000000000000)
      constant := (4145853226471688987768764771469595663821187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252053294917672899217/100000000000000000000)
  centralHi := (126026647458836449609/50000000000000000000)
  directionLo := (253663875489956800107/100000000000000000000)
  directionHi := (63415968872489200027/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree080.table
  base := (-7268743313384509285727541135336595345463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-4074493905600597179472721543300000000000000)
      constant := (40306468397445089442096224386485068280723130) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree080.table
  base := (-7268810032705078083714208898770206213457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-418249652917938372354011980890000000000000)
      constant := (4266557582920086241765785471160259895540607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253663875489956800107/100000000000000000000)
  centralHi := (63415968872489200027/25000000000000000000)
  directionLo := (127632147183138407687/50000000000000000000)
  directionHi := (2042114354930214523/800000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree081.table
  base := (-7225456848972394303089859801138140908893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-4127145184595255619705578197780000000000000)
      constant := (41470049923998590994902808561321310954642430) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree081.table
  base := (-722551678247124017705715802517763519193/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-211824892048438849778690947085000000000000)
      constant := (2194475150163259011875375758773147937797715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127632147183138407687/50000000000000000000)
  centralHi := (2042114354930214523/800000000000000000)
  directionLo := (256854741494180201893/100000000000000000000)
  directionHi := (128427370747090100947/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree082.table
  base := (-7179201488012516541566264900608392847203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-4179796463589914059938434852260000000000000)
      constant := (42649753351866151160571214737407887504870530) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree082.table
  base := (-3589627658850195282882378072339398082407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-214524957637908513380375903725000000000000)
      constant := (2256515677433908736374763440675369493962057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256854741494180201893/100000000000000000000)
  centralHi := (128427370747090100947/50000000000000000000)
  directionLo := (25843540097628082509/10000000000000000000)
  directionHi := (258435400976280825091/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree083.table
  base := (-7129977737709826916405098141362960160261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-4232447742584572500171291506740000000000000)
      constant := (43845578432517343990629755478013149521472110) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree083.table
  base := (-7130026078072205523903318002387985945951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-434450046454756353964121720730000000000000)
      constant := (4638800724999680451332862140062988688648401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25843540097628082509/10000000000000000000)
  centralHi := (258435400976280825091/100000000000000000000)
  directionLo := (260006451319000866269/100000000000000000000)
  directionHi := (26000645131900086627/10000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree084.table
  base := (-88472325716297965051092786904543046517/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (13500327947348318008424783200000000000000)
      linear := (-612157003082747277200592594460000000000000)
      constant := (6436789277274972673514672814706558939504800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree084.table
  base := (-707782946185742973956977650242875271453/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (45)
      previous := (18)
      next := (0)
      square := (675016397367415900421239160000000000000)
      linear := (-31417869830978262940535116715000000000000)
      constant := (340447027943345747841714827241499365499145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260006451319000866269/100000000000000000000)
  centralHi := (26000645131900086627/10000000000000000000)
  directionLo := (261568065667865660767/100000000000000000000)
  directionHi := (8174002052120801899/3125000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree085.table
  base := (-1404525372642249463885276846126219143499/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-4337750300573889380637004815700000000000000)
      constant := (46285592673044362374231636412665763098427450) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree085.table
  base := (-140453316608808861255289534037118269291/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-222625154406317504185430773645000000000000)
      constant := (2447702167890731457726473148754530120118525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261568065667865660767/100000000000000000000)
  centralHi := (8174002052120801899/3125000000000000000)
  directionLo := (131560206015114804023/50000000000000000000)
  directionHi := (263120412030229608047/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree086.table
  base := (-435281283350110184941728204408038518049/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-4390401579568547820869861470180000000000000)
      constant := (47529781443572849178160157652934978018495840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree086.table
  base := (-1741133878082874894806680980508546921021/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-225325219995787167787115730285000000000000)
      constant := (2513119271313272669069226163850162401739942) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131560206015114804023/50000000000000000000)
  centralHi := (263120412030229608047/100000000000000000000)
  directionLo := (132331826743122073019/50000000000000000000)
  directionHi := (264663653486244146039/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree087.table
  base := (-1725851853117512580124884465162651530121/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-4443052858563206261102718124660000000000000)
      constant := (48790091083952882689618999667342203000962840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree087.table
  base := (-3451719403363363861640736695987869964389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-228025285585256831388800686925000000000000)
      constant := (2579380498540738722279301432866594371744939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132331826743122073019/50000000000000000000)
  centralHi := (264663653486244146039/100000000000000000000)
  directionLo := (26619794838881765579/10000000000000000000)
  directionHi := (266197948388817655791/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree088.table
  base := (-3419673906629882258457636468507372050193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-4495704137557864701335574779140000000000000)
      constant := (50066521440597071903143480277238775390810860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree088.table
  base := (-3419687993333674378532690139460368928781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-230725351174726494990485643565000000000000)
      constant := (2646485842883619696434350904206441922489731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26619794838881765579/10000000000000000000)
  centralHi := (266197948388817655791/100000000000000000000)
  directionLo := (1673271565957883071/625000000000000000)
  directionHi := (267723450553261291361/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree089.table
  base := (-270892880883574418081281905273833683723/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-4548355416552523141568431433620000000000000)
      constant := (51359072373307373915912175827834537374393250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree089.table
  base := (-3386173650921848893529927381129741979161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-233425416764196158592170600205000000000000)
      constant := (2714435298224502381425580028474642643021111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1673271565957883071/625000000000000000)
  centralHi := (267723450553261291361/100000000000000000000)
  directionLo := (134620154718631803877/50000000000000000000)
  directionHi := (53848061887452721551/20000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree090.table
  base := (-6702330300623861727632186415078778300293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-4601006695547181581801288088100000000000000)
      constant := (52667743753867927163051747328861398632856430) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree090.table
  base := (-209448530658888427896939067013506024911/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-236125482353665822193855556845000000000000)
      constant := (2783228858957084732706778549761411276469776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134620154718631803877/50000000000000000000)
  centralHi := (53848061887452721551/20000000000000000000)
  directionLo := (67687167577947508521/25000000000000000000)
  directionHi := (54149734062358006817/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree091.table
  base := (-1325874577726369387478922802976295633173/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (13500327947348318008424783200000000000000)
      linear := (-664808282077405717433449248940000000000000)
      constant := (7713219352113161161951360237645296528389450) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree091.table
  base := (-3314696617283342516233186894253927430107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (45)
      previous := (18)
      next := (0)
      square := (675016397367415900421239160000000000000)
      linear := (-34117935420447926542220073355000000000000)
      constant := (407552359990289543799331926810222507989251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67687167577947508521/25000000000000000000)
  centralHi := (54149734062358006817/20000000000000000000)
  directionLo := (54449734884692061083/20000000000000000000)
  directionHi := (34031084302932538177/12500000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree092.table
  base := (-102397656347852257848098878703342157927/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-4706309253536498462267001397060000000000000)
      constant := (55333447398206854901465589906979189927409280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree092.table
  base := (-1310693651155782025981401816082066663087/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-483051227065210298794450940250000000000000)
      constant := (5846696552817723336328274698499893667543685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54449734884692061083/20000000000000000000)
  centralHi := (34031084302932538177/12500000000000000000)
  directionLo := (17108778696807347643/6250000000000000000)
  directionHi := (273740459148917562289/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree093.table
  base := (-323728092803702290896607215170198534437/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-4758960532531156902499858051540000000000000)
      constant := (56690479454858642682602032600503054362517400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree093.table
  base := (-6474578223264410895201568905305941015733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-488451358244149625997820853530000000000000)
      constant := (5989348248026556645227737237620008890229083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17108778696807347643/6250000000000000000)
  centralHi := (273740459148917562289/100000000000000000000)
  directionLo := (275224158141666626479/100000000000000000000)
  directionHi := (3440301976770832831/1250000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree094.table
  base := (-1598177156210049392405710899378168649769/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-4811611811525815342732714706020000000000000)
      constant := (58063631543228306601288126866192789446452760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree094.table
  base := (-6392723302170518183219376821022330686967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-493851489423088953201190766810000000000000)
      constant := (6133688117398334328000437738369905796338617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275224158141666626479/100000000000000000000)
  centralHi := (3440301976770832831/1250000000000000000)
  directionLo := (276699901471825673051/100000000000000000000)
  directionHi := (69174975367956418263/25000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree095.table
  base := (-31539452425803346839733764836248529817/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-4864263090520473782965571360500000000000000)
      constant := (59452903578742008548331672548572644077934000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree095.table
  base := (-1261580729125081282842840436254962196857/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-499251620602028280404560680090000000000000)
      constant := (6279716153429775838053941502417534261770035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276699901471825673051/100000000000000000000)
  centralHi := (69174975367956418263/25000000000000000000)
  directionLo := (34770976969900609943/12500000000000000000)
  directionHi := (55633563151840975909/20000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree096.table
  base := (-1555026899223992377878990297113080906697/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-4916914369515132223198428014980000000000000)
      constant := (60858295483068099457412746147482361422873880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree096.table
  base := (-6220119395962094982246071567473469720113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-504651751780967607607930593370000000000000)
      constant := (6427432349146563225079307227273799983714463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34770976969900609943/12500000000000000000)
  centralHi := (55633563151840975909/20000000000000000000)
  directionLo := (8738375759378043961/3125000000000000000)
  directionHi := (279628024300097406753/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree097.table
  base := (-6129360108446761624746172200160277482841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-4969565648509790663431284669460000000000000)
      constant := (62279807183490254152567652732792464033407910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree097.table
  base := (-3064685342903468314706596999805176334187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-255025941479953467405650253325000000000000)
      constant := (3288418349025002602356861335479546359624837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8738375759378043961/3125000000000000000)
  centralHi := (279628024300097406753/100000000000000000000)
  directionLo := (281080647188142038891/100000000000000000000)
  directionHi := (70270161797035509723/25000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree098.table
  base := (-6035648157894684336550042820827488949603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (13500327947348318008424783200000000000000)
      linear := (-717459561072064157666305903420000000000000)
      constant := (9102491230335495672232741494780075773527790) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree098.table
  base := (-188614301220247677723203354807415606603/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (45)
      previous := (18)
      next := (0)
      square := (675016397367415900421239160000000000000)
      linear := (-36818001009917590143905029995000000000000)
      constant := (480566371004970718194090562681569452060464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281080647188142038891/100000000000000000000)
  centralHi := (70270161797035509723/25000000000000000000)
  directionLo := (282525801429592791701/100000000000000000000)
  directionHi := (141262900714796395851/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree099.table
  base := (-2969485937009982510849144907889895048281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-5074868206499107543896997978420000000000000)
      constant := (65171189706540434702959708124476902852684620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree099.table
  base := (-2969490185848206422883437726146493726343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-260426072658892794609020166605000000000000)
      constant := (3440354915760380795631816259868821807409193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282525801429592791701/100000000000000000000)
  centralHi := (141262900714796395851/50000000000000000000)
  directionLo := (56792720210661722313/20000000000000000000)
  directionHi := (141981800526654305783/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree100.table
  base := (-1167866275441884047176681818962782187489/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-5127519485493765984129854632900000000000000)
      constant := (66641060407076609032269882720041183640651950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree100.table
  base := (-5839338992654266197359458216160281927739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-526252276496724916421410246490000000000000)
      constant := (7035178605067328277841231761408146185540789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56792720210661722313/20000000000000000000)
  centralHi := (141981800526654305783/50000000000000000000)
  directionLo := (285394157215755779881/100000000000000000000)
  directionHi := (142697078607877889941/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree101.table
  base := (-229469071210677045226243894430004508813/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-5180170764488424424362711287380000000000000)
      constant := (68127050658683093379299872865771444767040750) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree101.table
  base := (-114734672087942958630697357892491498497/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-265826203837832121812390079885000000000000)
      constant := (3595667754843991333579474801171697914341175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (285394157215755779881/100000000000000000000)
  centralHi := (142697078607877889941/50000000000000000000)
  directionLo := (28681757830129666261/10000000000000000000)
  directionHi := (286817578301296662611/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree102.table
  base := (-2815579094568550386082622984423648100917/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-5232822043483082864595567941860000000000000)
      constant := (69629160409447024891636721797590824861101340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree102.table
  base := (-5631164303583362080238766867911884521651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-537052538854603570828150073050000000000000)
      constant := (7349180540646467861651448585912317658439101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28681757830129666261/10000000000000000000)
  centralHi := (286817578301296662611/100000000000000000000)
  directionLo := (57646794003604175253/20000000000000000000)
  directionHi := (144116985009010438133/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree103.table
  base := (-552262570355174819373153433696322720433/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-5285473322477741304828424596340000000000000)
      constant := (71147389610499819592953296600749018669878300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree103.table
  base := (-1380657795399163310413861712998349931029/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-271226335016771449015759993165000000000000)
      constant := (3754356846732490188003849209016161706759158) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57646794003604175253/20000000000000000000)
  centralHi := (144116985009010438133/50000000000000000000)
  directionLo := (289643435489358661707/100000000000000000000)
  directionHi := (72410858872339665427/25000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree104.table
  base := (-5411129417607554558930478572466560159387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-5338124601472399745061281250820000000000000)
      constant := (72681738215734101263097594382635385521900370) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree104.table
  base := (-541113432503038344325358651294304006083/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-273926400606241112617444949805000000000000)
      constant := (3834967481950222735440866922032895518509665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289643435489358661707/100000000000000000000)
  centralHi := (72410858872339665427/25000000000000000000)
  directionLo := (145523037670850579963/50000000000000000000)
  directionHi := (291046075341701159927/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree105.table
  base := (-5296669420282585224765392724000831419723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (13500327947348318008424783200000000000000)
      linear := (-770110840066722597899162557900000000000000)
      constant := (10604600883078659696733998751344941800619390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree105.table
  base := (-5296673816119670215820933550545663753297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (90)
      previous := (36)
      next := (0)
      square := (1350032794734831800842478320000000000000)
      linear := (-79036133198774507491179973270000000000000)
      constant := (1118977763989048912466422175246180353726921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145523037670850579963/50000000000000000000)
  centralHi := (291046075341701159927/100000000000000000000)
  directionLo := (58488397557647654611/20000000000000000000)
  directionHi := (9138812118382446033/3125000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree106.table
  base := (-5179245795898294646162201474307323872939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-5443427159461716625526994559780000000000000)
      constant := (75798793466631856752160784136543411302259890) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree106.table
  base := (-2589624866563660565888341935982461639733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-279326531785180439820814863085000000000000)
      constant := (3998720920849396777054410983276859379653083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58488397557647654611/20000000000000000000)
  centralHi := (9138812118382446033/3125000000000000000)
  directionLo := (36728908588651472669/12500000000000000000)
  directionHi := (293831268709211781353/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree107.table
  base := (-5058858624533017288985188774337293231079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-5496078438456375065759851214260000000000000)
      constant := (77381500031739433999892473878055726316771290) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree107.table
  base := (-126471553767218437954567658265492533363/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-282026597374650103422499819725000000000000)
      constant := (4081863720784832153193651244869817317304260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36728908588651472669/12500000000000000000)
  centralHi := (293831268709211781353/100000000000000000000)
  directionLo := (922543786652404041/312500000000000000)
  directionHi := (295214011728769293121/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree108.table
  base := (-616938497799030831779198903821445596087/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-5548729717451033505992707868740000000000000)
      constant := (78980325839532657804843434546775933263338960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree108.table
  base := (-1233877785030093262440357633656032210253/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-284726662964119767024184776365000000000000)
      constant := (4165850572020724207019498872741708843395206) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (922543786652404041/312500000000000000)
  centralHi := (295214011728769293121/100000000000000000000)
  directionLo := (148295154144296678221/50000000000000000000)
  directionHi := (296590308288593356443/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree109.table
  base := (-4809193942140421951455146420529256770089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-5601380996445691946225564523220000000000000)
      constant := (80595270854405952954335274729719664182656390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree109.table
  base := (-961839353939162566977058818122022952043/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-574853457107178861251739466010000000000000)
      constant := (8501362945768740206753658291060104376749465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148295154144296678221/50000000000000000000)
  centralHi := (296590308288593356443/100000000000000000000)
  directionLo := (148980123859234796499/50000000000000000000)
  directionHi := (297960247718469592999/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree110.table
  base := (-4679916573198419710911966022237069815901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-5654032275440350386458421177700000000000000)
      constant := (82226335042343089948539559704653835790208510) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree110.table
  base := (-4679919104893077788034441220040546663007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-580253588286118188455109379290000000000000)
      constant := (8672712843543116659721757059618013213512657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148980123859234796499/50000000000000000000)
  centralHi := (297960247718469592999/100000000000000000000)
  directionLo := (299323917303947964299/100000000000000000000)
  directionHi := (2993239173039479643/1000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree111.table
  base := (-2273837971005241709947546883276368587659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-5706683554435008826691277832180000000000000)
      constant := (83873518370786389478683678043458158784094180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree111.table
  base := (-909535641723270153765062204388248688631/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-585653719465057515658479292570000000000000)
      constant := (8845750834282272812822088535304879071285405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299323917303947964299/100000000000000000000)
  centralHi := (2993239173039479643/1000000000000000000)
  directionLo := (150340701175621097039/50000000000000000000)
  directionHi := (300681402351242194079/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree112.table
  base := (-4412472112283911647002194770141095178733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (13500327947348318008424783200000000000000)
      linear := (-822762119061381038132019212380000000000000)
      constant := (12219545829788467892307824834138123337488690) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree112.table
  base := (-4412474141394959166490139563854504117497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (90)
      previous := (36)
      next := (0)
      square := (1350032794734831800842478320000000000000)
      linear := (-84436264377713834694549886550000000000000)
      constant := (1288639559288610231997467592973018471177521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150340701175621097039/50000000000000000000)
  centralHi := (300681402351242194079/100000000000000000000)
  directionLo := (151016393124751948323/50000000000000000000)
  directionHi := (302032786249503896647/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree113.table
  base := (-4274305145204458337246717188161776314879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-5811986112424325707156991141140000000000000)
      constant := (87216242325560727817896257495151729605709290) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree113.table
  base := (-33393023137204125082056175759694489667/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-298226990911468085032609559565000000000000)
      constant := (4598445541449392533379035993607598080404288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151016393124751948323/50000000000000000000)
  centralHi := (302032786249503896647/100000000000000000000)
  directionLo := (37922268816325006657/12500000000000000000)
  directionHi := (303378150530600053257/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree114.table
  base := (-2066587549815036459165308364417672537141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-5864637391418984147389847795620000000000000)
      constant := (88911782893070351974334170714984680913601820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree114.table
  base := (-2066588362707866795163731012322851809807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-300927056500937748634294516205000000000000)
      constant := (4687496667579608601482899066296180261319457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37922268816325006657/12500000000000000000)
  centralHi := (303378150530600053257/100000000000000000000)
  directionLo := (304717574926515094573/100000000000000000000)
  directionHi := (152358787463257547287/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree115.table
  base := (-199454101613265901010864657961537100847/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-5917288670413642587622704450100000000000000)
      constant := (90623442483262912026786447612601936411699400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree115.table
  base := (-159563339494521432176483096211492144253/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-607254244180814824471958945690000000000000)
      constant := (9554783669135612297581444547240922123290075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304717574926515094573/100000000000000000000)
  centralHi := (152358787463257547287/50000000000000000000)
  directionLo := (306051137424491948109/100000000000000000000)
  directionHi := (30605113742449194811/10000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree116.table
  base := (-960506499454636236860391129952295321133/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-5969939949408301027855561104580000000000000)
      constant := (92351221069331315836031027348177501170579320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree116.table
  base := (-960506825012786085257658695658488360161/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-306327187679877075837664429485000000000000)
      constant := (4868131041124130987939802461065468140704222) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306051137424491948109/100000000000000000000)
  centralHi := (30605113742449194811/10000000000000000000)
  directionLo := (38422364290002494909/12500000000000000000)
  directionHi := (307378914320019959273/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree117.table
  base := (-1846003524571838988061548802718548583037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-6022591228402959468088417759060000000000000)
      constant := (94095118625377140506769273192226822388623740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree117.table
  base := (-3692008214484776053008262270480515840843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-618054506538693478878698772250000000000000)
      constant := (9919428571997935112071847979686454723798693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38422364290002494909/12500000000000000000)
  centralHi := (307378914320019959273/100000000000000000000)
  directionLo := (308700980267771560651/100000000000000000000)
  directionHi := (77175245066942890163/25000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree118.table
  base := (-707805047473650978789482585551105872331/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-6075242507397617908321274413540000000000000)
      constant := (95855135126347892523035280094045790612789050) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree118.table
  base := (-442378285016585703734314916083345265437/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-311727318858816403041034342765000000000000)
      constant := (5052141567980331363185612653187664327974348) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308700980267771560651/100000000000000000000)
  centralHi := (77175245066942890163/25000000000000000000)
  directionLo := (310017408330583916129/100000000000000000000)
  directionHi := (31001740833058391613/10000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree119.table
  base := (-3383080612009190134297049139106645895511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (13500327947348318008424783200000000000000)
      linear := (-875413398056039478364875866860000000000000)
      constant := (13947324363997183401781657730569534787314230) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree119.table
  base := (-676616309004799266032306004824639884593/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (90)
      previous := (36)
      next := (0)
      square := (1350032794734831800842478320000000000000)
      linear := (-89836395556653161897919799830000000000000)
      constant := (1470117967397573968444237546131137604039245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310017408330583916129/100000000000000000000)
  centralHi := (31001740833058391613/10000000000000000000)
  directionLo := (62265654005315295327/20000000000000000000)
  directionHi := (77832067506644119159/25000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree120.table
  base := (-3224173221077565862935944541867237311871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-6180545065386934788786987722500000000000000)
      constant := (99423524866748884113853915483885053717183210) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree120.table
  base := (-3224174055835519841943178246354557590747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-634254900075511460488808512090000000000000)
      constant := (10479056477177836497571540218728626678053397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62265654005315295327/20000000000000000000)
  centralHi := (77832067506644119159/25000000000000000000)
  directionLo := (9769801105452825853/3125000000000000000)
  directionHi := (312633635374490427297/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree121.table
  base := (-3062303111173613224602347432822217433833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-6233196344381593229019844376980000000000000)
      constant := (101231898059819580166260472538316113457421830) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree121.table
  base := (-3062303857971032279160730485795746451399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-639655031254450787692178425370000000000000)
      constant := (10668975249920333852173735435776008423881449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9769801105452825853/3125000000000000000)
  centralHi := (312633635374490427297/100000000000000000000)
  directionLo := (313933572937331357869/100000000000000000000)
  directionHi := (31393357293733135787/10000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree122.table
  base := (-2897470327572918663617888402655462886457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-6285847623376251669252701031460000000000000)
      constant := (103056390105007334611973676287844823185636070) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree122.table
  base := (-2897470995633365112481195060493998736523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-645055162433390114895548338650000000000000)
      constant := (10860582087844571100853565066475794061910373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313933572937331357869/100000000000000000000)
  centralHi := (31393357293733135787/10000000000000000000)
  directionLo := (78807037466098032003/25000000000000000000)
  directionHi := (315228149864392128013/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree123.table
  base := (-2729674914304777034063251508373798220063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-6338498902370910109485557685940000000000000)
      constant := (104897000980737792972493991544537838872169130) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree123.table
  base := (-1364837755945036948746908867748573891469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-325227646806164721049459125965000000000000)
      constant := (5526938494420119010693578034170319879318019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78807037466098032003/25000000000000000000)
  centralHi := (315228149864392128013/100000000000000000000)
  directionLo := (158258715965864403053/50000000000000000000)
  directionHi := (316517431931728806107/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree124.table
  base := (-319864614277939068062631339336915681603/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-6391150181365568549718414340420000000000000)
      constant := (106753730666012336385625737465683290528116240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree124.table
  base := (-639729362183340650361442800098986880279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (315)
      previous := (126)
      next := (0)
      square := (4725114781571911302948674120000000000000)
      linear := (-327927712395634384651144082605000000000000)
      constant := (5624429975424858309689698489790299285732658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158258715965864403053/50000000000000000000)
  centralHi := (316517431931728806107/100000000000000000000)
  directionLo := (31780148358115871661/10000000000000000000)
  directionHi := (317801483581158716611/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree125.table
  base := (-596299092268374761808201344551534926161/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-6443801460360226989951270994900000000000000)
      constant := (108626579140376221663741169566553991544724440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree125.table
  base := (-2385196847134865903459416764177662965519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-661255555970208096505658078490000000000000)
      constant := (11445530971865396795553292096055294514689569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31780148358115871661/10000000000000000000)
  centralHi := (317801483581158716611/100000000000000000000)
  directionLo := (159540183978923009609/50000000000000000000)
  directionHi := (319080367957846019219/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree126.table
  base := (-552128329887132886338110857540272323231/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (13500327947348318008424783200000000000000)
      linear := (-928064677050697918597732521340000000000000)
      constant := (15787935197698498465046323308690723749495320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree126.table
  base := (-69016054596744529837595086921477801389/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (45)
      previous := (18)
      next := (0)
      square := (675016397367415900421239160000000000000)
      linear := (-47618263367796244550644856555000000000000)
      constant := (831706432137658409535478234884794486244432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159540183978923009609/50000000000000000000)
  centralHi := (319080367957846019219/100000000000000000000)
  directionLo := (320354146946536847651/100000000000000000000)
  directionHi := (80088536736634211913/25000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree127.table
  base := (-81154712213845198111152708771437573441/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-6549104018349543870416984303860000000000000)
      constant := (112420632377100354402554780352650889725347750) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree127.table
  base := (-2028868187693132763067998827296823651697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-672055818328086750912397905050000000000000)
      constant := (11843937183120411675837630427402455641066847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320354146946536847651/100000000000000000000)
  centralHi := (80088536736634211913/25000000000000000000)
  directionLo := (64324576241300568443/20000000000000000000)
  directionHi := (40202860150812855277/12500000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree128.table
  base := (-1846259865217293125769689274663365154601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-6601755297344202310649840958340000000000000)
      constant := (114341837101020827665866418237750951074245510) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree128.table
  base := (-1846260207121672745751519201454933753257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-677455949507026078115767818330000000000000)
      constant := (12045672369573429335118733032408708246090407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell004.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64324576241300568443/20000000000000000000)
  centralHi := (40202860150812855277/12500000000000000000)
  directionLo := (322886630205248904801/100000000000000000000)
  directionHi := (161443315102624452401/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree129.table
  base := (-830344768506082560336748032552496546803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4900000000000000000000000000000000000000000
      center := (6363)
      previous := (2457)
      next := (0)
      square := (94502295631438226058973482400000000000000)
      linear := (-6654406576338860750882697612820000000000000)
      constant := (116279160537104338457648442211417553384133060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree129.table
  base := (-1660689842733327321776837537881183344211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (630)
      previous := (252)
      next := (0)
      square := (9450229563143822605897348240000000000000)
      linear := (-682856080685965405319137731610000000000000)
      constant := (12249095607456028472812764655343822016133661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell004.Kernel129
