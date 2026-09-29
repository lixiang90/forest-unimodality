import ForestUnimodality.FiniteKernelDegreeCertificate
import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell296.Parameters
import ForestUnimodality.BinomialMassData.Q123_203.Batch000_049
import ForestUnimodality.BinomialMassData.Q123_203.Batch050_099
import ForestUnimodality.BinomialMassData.Q123_203.Batch100_149
import ForestUnimodality.BinomialMassData.Q63_103.Batch000_049
import ForestUnimodality.BinomialMassData.Q63_103.Batch050_099
import ForestUnimodality.BinomialMassData.Q63_103.Batch100_149

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree000.table
  base := (3692820580863957167448319351/200000000000000000000000000)
  polynomial :=
    { denominator := 2030000000000000000000000000000000000000000
      center := (5781)
      previous := (0)
      next := (3760)
      square := (27404741058402671063931600000000000000000)
      linear := (-90486663172420924647343376740000000000000)
      constant := (37482128895769165249600441412650000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree000.table
  base := (3692820580863957167448319351/200000000000000000000000000)
  polynomial :=
    { denominator := 1030000000000000000000000000000000000000000
      center := (2961)
      previous := (0)
      next := (1880)
      square := (13904868615839778914211600000000000000000)
      linear := (-45911952250046084919588018740000000000000)
      constant := (19018025991449379412358844657650000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree000.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel000

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree001.table
  base := (151638767792009462281185249578498834715721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-25110358924368504785137879078220000000000000)
      constant := (6262054237212961044830317324019378479800146689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree001.table
  base := (37832003614735875123265083614769144089519/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-6480944527350558889908227530220000000000000)
      constant := (1608867168323929821270233520256963398582828284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree001.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel001

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (48737477273829643571/100000000000000000000)
  directionHi := (12184369318457410893/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree002.table
  base := (124520712684293622271266281543484457324039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-31851925224735561866865052678220000000000000)
      constant := (5161803350954812787453183222003491001866323151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree002.table
  base := (62005656952231559074491855160872919613413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-8232957972946371033098889130220000000000000)
      constant := (1323564174944936311900125820364641608357397034) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree002.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel002

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48737477273829643571/100000000000000000000)
  centralHi := (12184369318457410893/25000000000000000000)
  directionLo := (34462600678250190539/50000000000000000000)
  directionHi := (68925201356500381079/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree003.table
  base := (51121641128101205609291895745095747393919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-38593491525102618948592226278220000000000000)
      constant := (4265114558522986544681469418736361308712016142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree003.table
  base := (101616889362025271154842288712541769307617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-9984971418542183176289550730220000000000000)
      constant := (1091553227652192702436325457693215630584508753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree003.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel003

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34462600678250190539/50000000000000000000)
  centralHi := (68925201356500381079/100000000000000000000)
  directionLo := (84415786871006438293/100000000000000000000)
  directionHi := (42207893435503219147/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree004.table
  base := (83934149385422920059180166081855163711241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-45335057825469676030319399878220000000000000)
      constant := (3536040131534089646898546626223249441376530369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree004.table
  base := (83249332287228676451784541091867454796331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-11736984864137995319480212330220000000000000)
      constant := (903334937198145780907476565966101827934275579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree004.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel004

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84415786871006438293/100000000000000000000)
  centralHi := (42207893435503219147/50000000000000000000)
  directionLo := (97474954547659287143/100000000000000000000)
  directionHi := (12184369318457410893/12500000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree005.table
  base := (68870938686953511071168181408534633922147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-52076624125836733112046573478220000000000000)
      constant := (2944811702747589605223164234359403729297755723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree005.table
  base := (34084441798851371464507447348513979716201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-13488998309733807462670873930220000000000000)
      constant := (751061199477925946219148913743869621618352818) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree005.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel005

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97474954547659287143/100000000000000000000)
  centralHi := (12184369318457410893/12500000000000000000)
  directionLo := (54490156118067107557/50000000000000000000)
  directionHi := (21796062447226843023/20000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree006.table
  base := (2258839246078285907770575864927175685643/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-58818190426203790193773747078220000000000000)
      constant := (2467418064978320980042601929278719570741559675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree006.table
  base := (13944969403689191461365082593330605835757/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-15241011755329619605861535530220000000000000)
      constant := (628412597306303511773298840814297589246184052) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree006.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel006

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54490156118067107557/50000000000000000000)
  centralHi := (21796062447226843023/20000000000000000000)
  directionLo := (59690975335686980873/50000000000000000000)
  directionHi := (119381950671373961747/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree007.table
  base := (11564034827640768914575556864765399911323/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (167649)
      previous := (0)
      next := (109040)
      square := (794737490693677460854016400000000000000000)
      linear := (-9365679532367263896500131525460000000000000)
      constant := (297736521604339979805366419990515637111834004) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree007.table
  base := (45594545231045755638700682747519661347433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-16993025200925431749052197130220000000000000)
      constant := (530214388223455483302210812732776087234916697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree007.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel007

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59690975335686980873/50000000000000000000)
  centralHi := (119381950671373961747/100000000000000000000)
  directionLo := (64473622197607733953/50000000000000000000)
  directionHi := (128947244395215467907/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree008.table
  base := (18917188626672080510667025979184383666781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-72301323026937904357228094278220000000000000)
      constant := (1778869053712183478394333713064578533048756458) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree008.table
  base := (37213788895815622388883994593130401766217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-18745038646521243892242858730220000000000000)
      constant := (452232546313431720846175415283480432337796153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree008.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel008

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64473622197607733953/50000000000000000000)
  centralHi := (128947244395215467907/100000000000000000000)
  directionLo := (34462600678250190539/25000000000000000000)
  directionHi := (137850402713000762157/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree009.table
  base := (6176859322461845596822590462811374834239/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-79042889327304961438955267878220000000000000)
      constant := (1538313767077183475801742012761149727720774755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree009.table
  base := (30311101700577976172802136347290861723393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-20497052092117056035433520330220000000000000)
      constant := (391003159784078895709877601933988752023476337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree009.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel009

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34462600678250190539/25000000000000000000)
  centralHi := (137850402713000762157/100000000000000000000)
  directionLo := (73106215910744465357/50000000000000000000)
  directionHi := (29242486364297786143/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree010.table
  base := (25142398731454894483323469182658039302819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-85784455627672018520682441478220000000000000)
      constant := (1351631275210136479412623074938355141629868171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree010.table
  base := (24619352240351238286437138239578751766809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-22249065537712868178624181930220000000000000)
      constant := (343692231559947439422390731389890977494076681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree010.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel010

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73106215910744465357/50000000000000000000)
  centralHi := (29242486364297786143/20000000000000000000)
  directionLo := (77060717797997784189/50000000000000000000)
  directionHi := (154121435595995568379/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree011.table
  base := (10196316498647572056358142587879024615903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-92526021928039075602409615078220000000000000)
      constant := (1209918348379897239141848779337033450793493454) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree011.table
  base := (3983992961657783873338012138802611968607/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-24001078983308680321814843530220000000000000)
      constant := (307980891967102946330598153689604551874758315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree011.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel011

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77060717797997784189/50000000000000000000)
  centralHi := (154121435595995568379/100000000000000000000)
  directionLo := (6465757013830652247/4000000000000000000)
  directionHi := (1262843166763799267/781250000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree012.table
  base := (4114457638063901014609423764306255282783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-99267588228406132684136788678220000000000000)
      constant := (1105874035134683425703321786881425895792818588) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree012.table
  base := (16034070187903310876223970379292356701817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-25753092428904492465005505130220000000000000)
      constant := (281971517487827316561892343121352612249576553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree012.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel012

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6465757013830652247/4000000000000000000)
  centralHi := (1262843166763799267/781250000000000000)
  directionLo := (168831573742012876587/100000000000000000000)
  directionHi := (42207893435503219147/25000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree013.table
  base := (2638537175578265366660217837584476889903/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-106009154528773189765863962278220000000000000)
      constant := (1033510440364897198097569100952353540780063635) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree013.table
  base := (256305413637320174762550932462206484317/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-27505105874500304608196166730220000000000000)
      constant := (264110974951163511264321098672637429605952650) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree013.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel013

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (168831573742012876587/100000000000000000000)
  centralHi := (42207893435503219147/25000000000000000000)
  directionLo := (8786273667377683157/5000000000000000000)
  directionHi := (175725473347553663141/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree014.table
  base := (163718863074122005031025651247060918243/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (167649)
      previous := (0)
      next := (109040)
      square := (794737490693677460854016400000000000000000)
      linear := (-16107245832734320978227305125460000000000000)
      constant := (141130827394515865748047829647092648044578624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree014.table
  base := (10143725561109864167752014508432932041373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-29257119320096116751386828330220000000000000)
      constant := (253127874062438148981545567248644976026926157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree014.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel014

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8786273667377683157/5000000000000000000)
  centralHi := (175725473347553663141/100000000000000000000)
  directionLo := (91179470927175890533/50000000000000000000)
  directionHi := (182358941854351781067/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree015.table
  base := (4108003328091762313788738323944561790547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-119492287129507303929318309478220000000000000)
      constant := (965060344760734961851694995268162893653302646) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree015.table
  base := (1584263201432408149766338261618254634009/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-31009132765691928894577489930220000000000000)
      constant := (247981272276472908173403120796840317061007405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree015.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel015

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91179470927175890533/50000000000000000000)
  centralHi := (182358941854351781067/100000000000000000000)
  directionLo := (188759437817704666921/100000000000000000000)
  directionHi := (94379718908852333461/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree016.table
  base := (1581610346131624980885558495854952227493/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-126233853429874361011045483078220000000000000)
      constant := (961637375808123943107995218447066905371036148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree016.table
  base := (242707695561757697877011723279962221723/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-32761146211287741037768151530220000000000000)
      constant := (247818740358215863510506177996847980256482675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree016.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel016

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188759437817704666921/100000000000000000000)
  centralHi := (94379718908852333461/50000000000000000000)
  directionLo := (97474954547659287143/50000000000000000000)
  directionHi := (194949909095318574287/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree017.table
  base := (237172635721559965650932260429497851101/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-132975419730241418092772656678220000000000000)
      constant := (974932913432940692440479464364123538920422180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree017.table
  base := (2258521334205583579760487841950015790173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-34513159656883553180958813130220000000000000)
      constant := (251942078392871253087306584301035435035890714) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree017.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel017

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97474954547659287143/50000000000000000000)
  centralHi := (194949909095318574287/100000000000000000000)
  directionLo := (200949766726139885711/100000000000000000000)
  directionHi := (12559360420383742857/6250000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree018.table
  base := (3412975949201270485472990091199529815159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-139716986030608475174499830278220000000000000)
      constant := (1002719005549025227484363655970601424152887231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree018.table
  base := (3215450171912775813607764449301702076441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-36265173102479365324149474730220000000000000)
      constant := (259779284392858964278230909493801757328962569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree018.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel018

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (200949766726139885711/100000000000000000000)
  centralHi := (12559360420383742857/6250000000000000000)
  directionLo := (41355120813900228647/20000000000000000000)
  directionHi := (51693901017375285809/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree019.table
  base := (4473863559861980816997471600497537523/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-146458552330975532256227003878220000000000000)
      constant := (1043166263236941836207058767520050348178077184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree019.table
  base := (2118733054735386425257736803621155958679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-38017186548075177467340136330220000000000000)
      constant := (270861633166553827615787822981396843565625511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree019.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel019

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41355120813900228647/20000000000000000000)
  centralHi := (51693901017375285809/25000000000000000000)
  directionLo := (21244173819973361989/10000000000000000000)
  directionHi := (212441738199733619891/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree020.table
  base := (1339918966442572723874751628102758883191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-153200118631342589337954177478220000000000000)
      constant := (1094772192826423435343074866622886590817417919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree020.table
  base := (1190677467878456267330557529942509325481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-39769199993670989610530797930220000000000000)
      constant := (284804931989909085307745508447560081434027929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree020.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel020

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21244173819973361989/10000000000000000000)
  centralHi := (212441738199733619891/100000000000000000000)
  directionLo := (54490156118067107557/25000000000000000000)
  directionHi := (217960624472268430229/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree021.table
  base := (530925392436089154945995570403310248281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (167649)
      previous := (0)
      next := (109040)
      square := (794737490693677460854016400000000000000000)
      linear := (-22848812133101378059954478725460000000000000)
      constant := (165186065711520995109898526340024287431630247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree021.table
  base := (200796265808460870617774004355533049479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-41521213439266801753721459530220000000000000)
      constant := (301294190319921537636655456417435700243845422) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree021.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel021

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54490156118067107557/25000000000000000000)
  centralHi := (217960624472268430229/100000000000000000000)
  directionLo := (111671589394257168763/50000000000000000000)
  directionHi := (223343178788514337527/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree022.table
  base := (-80488283458159969627587469906617761903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-166683251232076703501408524678220000000000000)
      constant := (1226742746886820931131215852563676377299478546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree022.table
  base := (-136435817663348151190431516179610933141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-43273226884862613896912121130220000000000000)
      constant := (320071080266118408307025629263341015220614262) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree022.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel022

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111671589394257168763/50000000000000000000)
  centralHi := (223343178788514337527/100000000000000000000)
  directionLo := (228599031499206797691/100000000000000000000)
  directionHi := (57149757874801699423/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree023.table
  base := (-151203907379339838739438075909346691377/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-173424817532443760583135698278220000000000000)
      constant := (1305259287289697554066439319646718660975226035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree023.table
  base := (-426345419829651208913675192547678538989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-45025240330458426040102782730220000000000000)
      constant := (340923678495146146902195296118783356759731398) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree023.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel023

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228599031499206797691/100000000000000000000)
  centralHi := (57149757874801699423/25000000000000000000)
  directionLo := (233736729876569469123/100000000000000000000)
  directionHi := (58434182469142367281/25000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree024.table
  base := (-317709984425285204163190385825102967047/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-180166383832810817664862871878220000000000000)
      constant := (1391166510949416070764249946498613327323840708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree024.table
  base := (-169282240373639909588247917605797028139/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-46777253776054238183293444330220000000000000)
      constant := (363678073350383119099138103871840794627786792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree024.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel024

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233736729876569469123/100000000000000000000)
  centralHi := (58434182469142367281/25000000000000000000)
  directionLo := (59690975335686980873/25000000000000000000)
  directionHi := (238763901342747923493/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree025.table
  base := (-343824357895887608184407580234955157513/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-186907950133177874746590045478220000000000000)
      constant := (1483900513079623651894186373605988664570233915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree025.table
  base := (-895515059547792105906578085614042868631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-48529267221650050326484105930220000000000000)
      constant := (388191497038663274234217105694941238413387442) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree025.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel025

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59690975335686980873/25000000000000000000)
  centralHi := (238763901342747923493/100000000000000000000)
  directionLo := (243687386369148217857/100000000000000000000)
  directionHi := (121843693184574108929/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree026.table
  base := (-528031173051537695577843120270778993257/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-193649516433544931828317219078220000000000000)
      constant := (1582997296824968657885784599041565873867489148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree026.table
  base := (-27175735784993988146243258787417234939/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-50281280667245862469674767530220000000000000)
      constant := (414346704887972513528339072898063244362571920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree026.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel026

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243687386369148217857/100000000000000000000)
  centralHi := (121843693184574108929/50000000000000000000)
  directionLo := (24851334766254223399/10000000000000000000)
  directionHi := (248513347662542233991/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree027.table
  base := (-2459116887838585251309048073281559993377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-200391082733911988910044392678220000000000000)
      constant := (1688074927202632457111032977301680194232927207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree027.table
  base := (-2512423467610272452579117164301613918489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-52033294112841674612865429130220000000000000)
      constant := (442047374461290157087727343080664177938750199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree027.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel027

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24851334766254223399/10000000000000000000)
  centralHi := (248513347662542233991/100000000000000000000)
  directionLo := (791398001915685359/312500000000000000)
  directionHi := (253247360613019314881/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree028.table
  base := (-2767730529798058350913329738435628995511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (167649)
      previous := (0)
      next := (109040)
      square := (794737490693677460854016400000000000000000)
      linear := (-29590378433468435141681652325460000000000000)
      constant := (256974127257468000187753714785909452103426743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree028.table
  base := (-2813586178265600041814647235081311275931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-53785307558437486756056090730220000000000000)
      constant := (471214338804193355461692923740382368673648021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree028.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel028

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (791398001915685359/312500000000000000)
  centralHi := (253247360613019314881/100000000000000000000)
  directionLo := (257894488790430935813/100000000000000000000)
  directionHi := (128947244395215467907/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree029.table
  base := (-3044253187679656304415388251056979486963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14210000000000000000000000000000000000000000
      center := (40467)
      previous := (0)
      next := (26320)
      square := (191833187408818697447521200000000000000000)
      linear := (-7374972942574003554258577237180000000000000)
      constant := (66033451143739840769651993834268032149025577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree029.table
  base := (-385460363562089494853359957757488533693/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-55537321004033298899246752330220000000000000)
      constant := (501782502007907657845120242703186433168407704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree029.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel029

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257894488790430935813/100000000000000000000)
  centralHi := (128947244395215467907/50000000000000000000)
  directionLo := (262459347403545085841/100000000000000000000)
  directionHi := (131229673701772542921/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree030.table
  base := (-3293867078982501402310790013978739341033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-220615781635013160155225913478220000000000000)
      constant := (2036314950300249269658896634484550130495371103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree030.table
  base := (-332776136291018930935404749701075240529/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-57289334449629111042437413930220000000000000)
      constant := (533698312974261972595232385522812927732278390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree030.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel030

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262459347403545085841/100000000000000000000)
  centralHi := (131229673701772542921/50000000000000000000)
  directionLo := (53389231397543767067/20000000000000000000)
  directionHi := (33368269623464854417/12500000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree031.table
  base := (-3520845442831825236798296449756804895421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-227357347935380217236953087078220000000000000)
      constant := (2162677396286545994648323683911591827064596011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree031.table
  base := (-1774988053912116940924293083010294501853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-59041347895224923185628075530220000000000000)
      constant := (566917695909186369630337464763907571259683046) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree031.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel031

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53389231397543767067/20000000000000000000)
  centralHi := (33368269623464854417/12500000000000000000)
  directionLo := (135679394549733389651/50000000000000000000)
  directionHi := (271358789099466779303/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree032.table
  base := (-3728713769865617797193905301536457160761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-234098914235747274318680260678220000000000000)
      constant := (2293912139183644627818466018477624136862199951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree032.table
  base := (-1876874205930761896564501441984194078009/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-60793361340820735328818737130220000000000000)
      constant := (601404354573862899245107937383819370052805038) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree032.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel032

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135679394549733389651/50000000000000000000)
  centralHi := (271358789099466779303/100000000000000000000)
  directionLo := (275700805426001524313/100000000000000000000)
  directionHi := (137850402713000762157/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree033.table
  base := (-3920382209518766261668949726202957626119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-240840480536114331400407434278220000000000000)
      constant := (2429899254643482903444061170120562319185262129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree033.table
  base := (-3941897251716261058505289628419455713203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-62545374786416547472009398730220000000000000)
      constant := (637128382444542772259120098492557994338629373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree033.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel033

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275700805426001524313/100000000000000000000)
  centralHi := (137850402713000762157/50000000000000000000)
  directionLo := (27997549143373784341/10000000000000000000)
  directionHi := (279975491433737843411/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree034.table
  base := (-2049127167529200220491740023614795859363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-247582046836481388482134607878220000000000000)
      constant := (2570539693815295669153498225060395754863020266) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree034.table
  base := (-411674671348135067157251555658301649251/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-64297388232012359615200060330220000000000000)
      constant := (674065123291866359595323859401290778030961410) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree034.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel034

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27997549143373784341/10000000000000000000)
  centralHi := (279975491433737843411/100000000000000000000)
  directionLo := (56837177091963345861/20000000000000000000)
  directionHi := (142092942729908364653/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree035.table
  base := (-4264316512229104232343491106407040402249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (167649)
      previous := (0)
      next := (109040)
      square := (794737490693677460854016400000000000000000)
      linear := (-36331944733835492223408825925460000000000000)
      constant := (387964514364730623875259334551681753151960137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree035.table
  base := (-214010703380937257914443358369568623053/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-66049401677608171758390721930220000000000000)
      constant := (712194236793502806905828819542844929560614460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree035.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel035

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56837177091963345861/20000000000000000000)
  centralHi := (142092942729908364653/50000000000000000000)
  directionLo := (28833480397898054393/10000000000000000000)
  directionHi := (288334803978980543931/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree036.table
  base := (-4420211351863897521804309967195190122893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-261065179437215502645588955078220000000000000)
      constant := (2865467284507121080879558547566573410225702363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree036.table
  base := (-4433882017178234158975576606868667693501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-67801415123203983901581383530220000000000000)
      constant := (751498932052796895896467027080050304439647891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree036.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel036

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28833480397898054393/10000000000000000000)
  centralHi := (288334803978980543931/100000000000000000000)
  directionLo := (292424863642977861429/100000000000000000000)
  directionHi := (29242486364297786143/10000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree037.table
  base := (-456729809969583653764844604441256196541/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-267806745737582559727316128678220000000000000)
      constant := (3019630732519902296300433911699542733967419310) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree037.table
  base := (-4579057982435175069418418646849475939731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-69553428568799796044772045130220000000000000)
      constant := (791965338648047359955347197458513909755393821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree037.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel037

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292424863642977861429/100000000000000000000)
  centralHi := (29242486364297786143/10000000000000000000)
  directionLo := (59291700116502396167/20000000000000000000)
  directionHi := (74114625145627995209/25000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree038.table
  base := (-470670230280578922458062301138108427033/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-274548312037949616809043302278220000000000000)
      constant := (3178195561921802526256104476406756898303971030) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree038.table
  base := (-4716822764761317708352316728879112086197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-71305442014395608187962706730220000000000000)
      constant := (833581990357501305255510527886881499877536027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree038.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel038

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59291700116502396167/20000000000000000000)
  centralHi := (74114625145627995209/25000000000000000000)
  directionLo := (150218993688088855359/50000000000000000000)
  directionHi := (300437987376177710719/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree039.table
  base := (-2419678335573979937713266416905381306319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-281289878338316673890770475878220000000000000)
      constant := (3341123336668318966043516301473272283495800658) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree039.table
  base := (-4848070507052251355877650608481186480003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-73057455459991420331153368330220000000000000)
      constant := (876339401219179425124372089538803092633648173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree039.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel039

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150218993688088855359/50000000000000000000)
  centralHi := (300437987376177710719/100000000000000000000)
  directionLo := (1521827240110267727/500000000000000000)
  directionHi := (304365448022053545401/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree040.table
  base := (-993206941521743687284652167307269193519/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-288031444638683730972497649478220000000000000)
      constant := (3508382181479007196548185337747973719021377645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree040.table
  base := (-2486770760039455219524126615338086283547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-74809468905587232474344029930220000000000000)
      constant := (920229717276112876225317768700556485235699754) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree040.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel040

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1521827240110267727/500000000000000000)
  centralHi := (304365448022053545401/100000000000000000000)
  directionLo := (308242871191991136757/100000000000000000000)
  directionHi := (154121435595995568379/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree041.table
  base := (-5087378397323269457203745522670794487673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-294773010939050788054224823078220000000000000)
      constant := (3679945640788430573484287822456079229957483343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree041.table
  base := (-5093849259548516437568744433810941005819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-76561482351183044617534691530220000000000000)
      constant := (965246430376703745880161253507119726869266229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree041.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel041

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308242871191991136757/100000000000000000000)
  centralHi := (154121435595995568379/50000000000000000000)
  directionLo := (156036061001695614791/50000000000000000000)
  directionHi := (312072122003391229583/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree042.table
  base := (-260196050761891522861606318357903639237/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (167649)
      previous := (0)
      next := (109040)
      square := (794737490693677460854016400000000000000000)
      linear := (-43073511034202549305135999525460000000000000)
      constant := (550827391267047202727460861710660425516235620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree042.table
  base := (-1041900501176379644889654232785915493213/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-78313495796778856760725353130220000000000000)
      constant := (1011384142869467460575148504007911112662516415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree042.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel042

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156036061001695614791/50000000000000000000)
  centralHi := (312072122003391229583/100000000000000000000)
  directionLo := (6317099050124718803/2000000000000000000)
  directionHi := (315854952506235940151/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree043.table
  base := (-2658052960470768168611171112384036213397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-308256143539784902217679170278220000000000000)
      constant := (4035902205316398073248479260037392503364246054) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree043.table
  base := (-1330230902071194823765175582471411457933/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-80065509242374668903916014730220000000000000)
      constant := (1058638374051680499747858144948903183371155212) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree043.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel043

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6317099050124718803/2000000000000000000)
  centralHi := (315854952506235940151/100000000000000000000)
  directionLo := (319593011052703751699/100000000000000000000)
  directionHi := (3195930110527037517/1000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree044.table
  base := (-2712151027025808992495475713416669428577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-314997709840151959299406343878220000000000000)
      constant := (4220261836496947068297014954368504939035540814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree044.table
  base := (-5428463498884334079833647308848749734579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-81817522687970481047106676330220000000000000)
      constant := (1107005400884405669865883668447703614065851389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree044.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel044

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319593011052703751699/100000000000000000000)
  centralHi := (3195930110527037517/1000000000000000000)
  directionLo := (323287850691532612351/100000000000000000000)
  directionHi := (1262843166763799267/390625000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree045.table
  base := (-1382204178933541823066180932002698086147/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-321739276140519016381133517478220000000000000)
      constant := (4408857968837223923471664660148303258271873108) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree045.table
  base := (-5532414055205227128552529976744514250617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-83569536133566293190297337930220000000000000)
      constant := (1156482126838983804720551512604617448315204247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree045.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel045

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323287850691532612351/100000000000000000000)
  centralHi := (1262843166763799267/390625000000000000)
  directionLo := (163470468354201322671/50000000000000000000)
  directionHi := (326940936708402645343/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree046.table
  base := (-1125981223443406757154490867218320378617/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-328480842440886073462860691078220000000000000)
      constant := (4601680044128740187625461455658921177587860235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree046.table
  base := (-2816509142455651576162036895466799154657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-85321549579162105333487999530220000000000000)
      constant := (1207065973847109175771730448260505455536487774) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree046.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel046

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163470468354201322671/50000000000000000000)
  centralHi := (326940936708402645343/100000000000000000000)
  directionLo := (33055365341618114591/10000000000000000000)
  directionHi := (330553653416181145911/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree047.table
  base := (-715973011281701922553874008321248698771/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-335222408741253130544587864678220000000000000)
      constant := (4798719250578770086082596918062657298978766888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree047.table
  base := (-5730478721322554525931415211287359632219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-87073563024757917476678661130220000000000000)
      constant := (1258754793232789983915346180712592401661788629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree047.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel047

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33055365341618114591/10000000000000000000)
  centralHi := (330553653416181145911/100000000000000000000)
  directionLo := (83531827571067883623/25000000000000000000)
  directionHi := (334127310284271534493/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree048.table
  base := (-1455657321007351196725097160874017912037/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-341963975041620187626315038278220000000000000)
      constant := (4999968226233028649729480975863130383451469068) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree048.table
  base := (-5824964348284596407244140517204229548873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-88825576470353729619869322730220000000000000)
      constant := (1311546792246408097941560269122740328716006343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree048.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel048

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83531827571067883623/25000000000000000000)
  centralHi := (334127310284271534493/100000000000000000000)
  directionLo := (168831573742012876587/50000000000000000000)
  directionHi := (13506525899361030127/4000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree049.table
  base := (-5914591115184446418205607495672622225607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (167649)
      previous := (0)
      next := (109040)
      square := (794737490693677460854016400000000000000000)
      linear := (-49815077334569606386863173125460000000000000)
      constant := (743631544825885184049966844446115272957851591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree049.table
  base := (-2958308157850792106337705625338660411833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-90577589915949541763059984330220000000000000)
      constant := (1365440473428630333037645482691944303381727406) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree049.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel049

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (168831573742012876587/50000000000000000000)
  centralHi := (13506525899361030127/4000000000000000000)
  directionLo := (68232468183361501/20000000000000000)
  directionHi := (341162340916807505001/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree050.table
  base := (-6003794690174768416660997130078474263947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-355447107642354301789769385478220000000000000)
      constant := (5415071857711326538226825736217596154057008077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree050.table
  base := (-750694082517439028840571360487497731751/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-92329603361545353906250645930220000000000000)
      constant := (1420434584529528055796912286523705092510829128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree050.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel050

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68232468183361501/20000000000000000)
  centralHi := (341162340916807505001/100000000000000000000)
  directionLo := (21539125423906369087/6250000000000000000)
  directionHi := (344626006782501905393/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree051.table
  base := (-6090344880246792284221530330389382224747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-362188673942721358871496559078220000000000000)
      constant := (5628917036384225615686591977705003947900400877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree051.table
  base := (-6091872206481568192779771158246332346569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-94081616807141166049441307530220000000000000)
      constant := (1476528077115915527577063778793784660135249479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree051.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel051

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21539125423906369087/6250000000000000000)
  centralHi := (344626006782501905393/100000000000000000000)
  directionLo := (348055205738788096471/100000000000000000000)
  directionHi := (43506900717348512059/12500000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree052.table
  base := (-24697318789281966532863350635790250563/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-368930240243088415953223732678220000000000000)
      constant := (5846952722916683328138616098741469891137333250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree052.table
  base := (-6175657795130551133075418070244093030027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-95833630252736978192631969130220000000000000)
      constant := (1533720072333959453423907146285020417044443557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree052.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel052

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (348055205738788096471/100000000000000000000)
  centralHi := (43506900717348512059/12500000000000000000)
  directionLo := (351450946695107326281/100000000000000000000)
  directionHi := (175725473347553663141/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree053.table
  base := (-1251164618563158482501252148532702988907/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-375671806543455473034950906278220000000000000)
      constant := (6069175869844635947156229863223639212650657185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree053.table
  base := (-391061184590364847473188948679257757947/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-97585643698332790335822630730220000000000000)
      constant := (1592009832567904207964499930868248071135044432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree053.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel053

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (351450946695107326281/100000000000000000000)
  centralHi := (175725473347553663141/50000000000000000000)
  directionLo := (354814190279791701929/100000000000000000000)
  directionHi := (35481419027979170193/10000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree054.table
  base := (-1583721819971203526718835888696312868209/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-382413372843822530116678079878220000000000000)
      constant := (6295583913426297780891029416557934572055901276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree054.table
  base := (-6335894108943969367917084947067366852559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-99337657143928602479013292330220000000000000)
      constant := (1651396737960226798227885994350042305061201569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree054.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel054

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (354814190279791701929/100000000000000000000)
  centralHi := (35481419027979170193/10000000000000000000)
  directionLo := (179072926007060942619/50000000000000000000)
  directionHi := (358145852014121885239/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree055.table
  base := (-641157466178785142741158289664944768867/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-389154939144189587198405253478220000000000000)
      constant := (6526174694175715344593768894058072910197597970) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree055.table
  base := (-400778276527508065354532478627545352293/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-101089670589524414622203953930220000000000000)
      constant := (1711880266942620953203552793881945941720377008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree055.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel055

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179072926007060942619/50000000000000000000)
  centralHi := (358145852014121885239/100000000000000000000)
  directionLo := (361446805223034658139/100000000000000000000)
  directionHi := (18072340261151732907/5000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree056.table
  base := (-3242964717291571921976429182823574249473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (167649)
      previous := (0)
      next := (109040)
      square := (794737490693677460854016400000000000000000)
      linear := (-56556643634936663468590346725460000000000000)
      constant := (965849484402503521135985587913595236786704898) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree056.table
  base := (-1621673830268338848941010712639370214621/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-102841684035120226765394615530220000000000000)
      constant := (1773459980078222610231250804313155685572343244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree056.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel056

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (361446805223034658139/100000000000000000000)
  centralHi := (18072340261151732907/5000000000000000000)
  directionLo := (91179470927175890533/25000000000000000000)
  directionHi := (364717883708703562133/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree057.table
  base := (-819748615040441025555907019782971402171/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-402638071744923701361859600678220000000000000)
      constant := (6999897465347250337298327396498248251903482088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree057.table
  base := (-6558657743477456751155178846700974584951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-104593697480716038908585277130220000000000000)
      constant := (1836135506639411696706569996110689360628254841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree057.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel057

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91179470927175890533/25000000000000000000)
  centralHi := (364717883708703562133/100000000000000000000)
  directionLo := (5749373190784134759/1562500000000000000)
  directionHi := (367959884210184624577/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree058.table
  base := (-103559135579734180608028185523344506987/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 14210000000000000000000000000000000000000000
      center := (40467)
      previous := (0)
      next := (26320)
      square := (191833187408818697447521200000000000000000)
      linear := (-14116539242941060635985750837180000000000000)
      constant := (249759538527151636728442056173804957156574272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree058.table
  base := (-165709230294269752025030256220553307311/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-106345710926311851051775938730220000000000000)
      constant := (1899906533447252563543741976146205998509504040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree058.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel058

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5749373190784134759/1562500000000000000)
  centralHi := (367959884210184624577/100000000000000000000)
  directionLo := (185586784334842615151/50000000000000000000)
  directionHi := (371173568669685230303/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree059.table
  base := (-3347671712096187562910388265940742981869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-416121204345657815525313947878220000000000000)
      constant := (7490332745563533441151516667699875844920320758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree059.table
  base := (-6695854697163775778130991483532237896839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-108097724371907663194966600330220000000000000)
      constant := (1964772795582173860795245427807786488152435049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree059.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel059

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185586784334842615151/50000000000000000000)
  centralHi := (371173568669685230303/100000000000000000000)
  directionLo := (93589916580929873087/25000000000000000000)
  directionHi := (374359666323719492349/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree060.table
  base := (-6760687813834114691024811871901309828977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-422862770646024872607041121478220000000000000)
      constant := (7741814916699400223587052327912018923257686807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree060.table
  base := (-6761135351514114414438322430958166584703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-109849737817503475338157261930220000000000000)
      constant := (2030734068644117243093859028167164810702885873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree060.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel060

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93589916580929873087/25000000000000000000)
  centralHi := (374359666323719492349/100000000000000000000)
  directionLo := (188759437817704666921/50000000000000000000)
  directionHi := (377518875635409333843/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree061.table
  base := (-426489817235902975667243604481700539091/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-429604336946391929688768295078220000000000000)
      constant := (7997472338256384952385841763326837639753583696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree061.table
  base := (-1706057278960777985070696470516447847227/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-111601751263099287481347923530220000000000000)
      constant := (2097790162296787675612217963394984019155075028) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree061.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel061

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188759437817704666921/50000000000000000000)
  centralHi := (377518875635409333843/100000000000000000000)
  directionLo := (380651866082435907639/100000000000000000000)
  directionHi := (9516296652060897691/2500000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree062.table
  base := (-6884807556088768038731369403099167361179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-436345903246758986770495468678220000000000000)
      constant := (8257304336629066709857457136486926412213174589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree062.table
  base := (-1721287807113773654372717061288986102243/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-113353764708695099624538585130220000000000000)
      constant := (2165940914877014561038605039185580585765216052) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree062.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel062

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380651866082435907639/100000000000000000000)
  centralHi := (9516296652060897691/2500000000000000000)
  directionLo := (9593981995340157673/2500000000000000000)
  directionHi := (383759279813606306921/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree063.table
  base := (-433975823008024865605742702627349486347/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (167649)
      previous := (0)
      next := (109040)
      square := (794737490693677460854016400000000000000000)
      linear := (-63298209935303720550317520325460000000000000)
      constant := (1217330048351735838982228701005304697182003376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree063.table
  base := (-6943914649705898298854513632991723110331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-115105778154290911767729246730220000000000000)
      constant := (2235186188888382836810750520446650809522498421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree063.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel063

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9593981995340157673/2500000000000000000)
  centralHi := (383759279813606306921/100000000000000000000)
  directionLo := (9671043329641160093/2500000000000000000)
  directionHi := (386841733185646403721/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree064.table
  base := (-7000265770344328162822842662666531224599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-449829035847493100933949815878220000000000000)
      constant := (8789489855080730548406465063211454914765499809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree064.table
  base := (-1400106083501365458184098437649414986369/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-116857791599886723910919908330220000000000000)
      constant := (2305525867229691475540499722734566782048056395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree064.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel064

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9671043329641160093/2500000000000000000)
  centralHi := (386841733185646403721/100000000000000000000)
  directionLo := (97474954547659287143/25000000000000000000)
  directionHi := (389899818190637148573/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree065.table
  base := (-7054775483208852064617621521472966343367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-456570602147860158015676989478220000000000000)
      constant := (9061842469430263010648744161757920529956189297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree065.table
  base := (-881875993151673110840442036417265174091/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-118609805045482536054110569930220000000000000)
      constant := (2376959850034651942792047170225493870144548648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree065.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel065

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97474954547659287143/25000000000000000000)
  centralHi := (389899818190637148573/100000000000000000000)
  directionLo := (196467051891728759207/50000000000000000000)
  directionHi := (78586820756691503683/20000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree066.table
  base := (-7107150955364261872687490677013516126239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-463312168448227215097404163078220000000000000)
      constant := (9338367825108848035485995341866270013953817049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree066.table
  base := (-888419408942515140516445761367536677303/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-120361818491078348197301231530220000000000000)
      constant := (2449488052020541577213652098062134427123939784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree066.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel066

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196467051891728759207/50000000000000000000)
  centralHi := (78586820756691503683/20000000000000000000)
  directionLo := (395945137117664352143/100000000000000000000)
  directionHi := (24746571069854022009/6250000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree067.table
  base := (-7157399587400550379699439350194695144479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-470053734748594272179131336678220000000000000)
      constant := (9619065617145572609925204644732166807791164889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree067.table
  base := (-7157579270487587103244040284728860823983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-122113831936674160340491893130220000000000000)
      constant := (2523110400261088532184359348920851515518364353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree067.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel067

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (395945137117664352143/100000000000000000000)
  centralHi := (24746571069854022009/6250000000000000000)
  directionLo := (398933444697412009373/100000000000000000000)
  directionHi := (199466722348706004687/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree068.table
  base := (-1801381930059245490929681597604487586661/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-476795301048961329260858510278220000000000000)
      constant := (9903935584237494768210680818430626684165147404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree068.table
  base := (-7205685827901866937876903472738730196993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-123865845382269972483682554730220000000000000)
      constant := (2597826832313351701340695566539874811340101263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree068.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel068

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (398933444697412009373/100000000000000000000)
  centralHi := (199466722348706004687/50000000000000000000)
  directionLo := (200949766726139885711/50000000000000000000)
  directionHi := (401899533452279771423/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree069.table
  base := (-7251540793902597160722110731849122941709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-483536867349328386342585683878220000000000000)
      constant := (10192977502206457778895357604043609492695113819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree069.table
  base := (-725167999015999533432215610328458803303/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-125617858827865784626873216330220000000000000)
      constant := (2673637294640317123483608918163033805557584730) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree069.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel069

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (200949766726139885711/50000000000000000000)
  centralHi := (401899533452279771423/100000000000000000000)
  directionLo := (404843891741220677677/100000000000000000000)
  directionHi := (202421945870610338839/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree070.table
  base := (-7295443481534705454064198393477800508459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (167649)
      previous := (0)
      next := (109040)
      square := (794737490693677460854016400000000000000000)
      linear := (-70039776235670777632044693925460000000000000)
      constant := (1498027311211020893639953577447796188406701867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree070.table
  base := (-1823891522385879227906996850147969006889/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-127369872273461596770063877930220000000000000)
      constant := (2750541741280809891749617164310520787223658396) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree070.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel070

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (404843891741220677677/100000000000000000000)
  centralHi := (202421945870610338839/50000000000000000000)
  directionLo := (203883495145631067961/50000000000000000000)
  directionHi := (407766990291262135923/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree071.table
  base := (-3668619901303226467712685893901168696699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-497019999950062500506040031078220000000000000)
      constant := (10783576447411091320671576253866873478355461818) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree071.table
  base := (-7337347850092827713112667964030349554583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-129121885719057408913254539530220000000000000)
      constant := (2828540132726485444515156772193622021575428953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree071.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel071

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203883495145631067961/50000000000000000000)
  centralHi := (407766990291262135923/100000000000000000000)
  directionLo := (410669283076067584773/100000000000000000000)
  directionHi := (205334641538033792387/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree072.table
  base := (-7376933218725213876342977212587549376269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-503761566250429557587767204678220000000000000)
      constant := (11085133166358914688115278735655919677753330779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree072.table
  base := (-1475405695419657473318230004110295656033/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-130873899164653221056445201130220000000000000)
      constant := (2907632434972418356488738913636609366925729515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree072.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel072

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (410669283076067584773/100000000000000000000)
  centralHi := (205334641538033792387/50000000000000000000)
  directionLo := (41355120813900228647/10000000000000000000)
  directionHi := (413551208139002286471/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree073.table
  base := (-3707263357394323189963649932684575290987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-510503132550796614669494378278220000000000000)
      constant := (11390861212315968765039710744796462673667433434) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree073.table
  base := (-7414610732857013416175490325010934753577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-132625912610249033199635862730220000000000000)
      constant := (2987818618713398507644878778527218993199301607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree073.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel073

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41355120813900228647/10000000000000000000)
  centralHi := (413551208139002286471/100000000000000000000)
  directionLo := (83282637672985706649/20000000000000000000)
  directionHi := (208206594182464266623/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree074.table
  base := (-1862505716956212205657723873330479507873/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-517244698851163671751221551878220000000000000)
      constant := (11700760479085502645449638911503177079840246172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree074.table
  base := (-7450097000887547109350035934973553816703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-134377926055844845342826524330220000000000000)
      constant := (3069098658662677693889014928931745567558597873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree074.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel074

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83282637672985706649/20000000000000000000)
  centralHi := (208206594182464266623/50000000000000000000)
  directionLo := (419255632204580542067/100000000000000000000)
  directionHi := (104813908051145135517/25000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree075.table
  base := (-7483423905460747749750728650954523284819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-523986265151530728832948725478220000000000000)
      constant := (12014830874869238313339920623449315049955893829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree075.table
  base := (-3741744670216205256035529293538992636841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-136129939501440657486017185930220000000000000)
      constant := (3151472532973751998623417277996189654231507662) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree075.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel075

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (419255632204580542067/100000000000000000000)
  centralHi := (104813908051145135517/25000000000000000000)
  directionLo := (422078934355032191467/100000000000000000000)
  directionHi := (105519733588758047867/25000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree076.table
  base := (-3757365877822560233662795665549088465071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-530727831451897785914675899078220000000000000)
      constant := (12333072320218334604706003301402295226885778322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree076.table
  base := (-7514789532777960841866490084874907899981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-137881952947036469629207847530220000000000000)
      constant := (3234940222748954458127331997216682102089101571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree076.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel076

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (422078934355032191467/100000000000000000000)
  centralHi := (105519733588758047867/25000000000000000000)
  directionLo := (424883476399467239781/100000000000000000000)
  directionHi := (212441738199733619891/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree077.table
  base := (-1508789617797672664030924683507597560627/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (167649)
      previous := (0)
      next := (109040)
      square := (794737490693677460854016400000000000000000)
      linear := (-76781342536037834713771867525460000000000000)
      constant := (1807926392326943956653579884270173865802944255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree077.table
  base := (-7543999120671193444110954369744476647179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-139633966392632281772398509130220000000000000)
      constant := (3319501711621282198781679701199120847250077989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree077.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel077

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (424883476399467239781/100000000000000000000)
  centralHi := (212441738199733619891/50000000000000000000)
  directionLo := (106917406852297002363/25000000000000000000)
  directionHi := (427669627409188009453/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree078.table
  base := (-7571074354861069597893440397145309235207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-544210964052631900078130246278220000000000000)
      constant := (12982068093352944810073670030317598951726354737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree078.table
  base := (-7571119441905443363609386017213823236471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-141385979838228093915589170730220000000000000)
      constant := (3405156985398085729096124839031738549284279161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree078.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel078

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106917406852297002363/25000000000000000000)
  centralHi := (427669627409188009453/100000000000000000000)
  directionLo := (430437744510551440679/100000000000000000000)
  directionHi := (10760943612763786017/2500000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree079.table
  base := (-7596111812210096337969111789325364811653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-550952530352998957159857419878220000000000000)
      constant := (13312822309531404913546503714856271041476591523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree079.table
  base := (-7596151657974032105454908112287257370749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-143137993283823906058779832330220000000000000)
      constant := (3491906031757082401223134467905724486553723859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree079.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel079

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (430437744510551440679/100000000000000000000)
  centralHi := (10760943612763786017/2500000000000000000)
  directionLo := (43318817341929802261/10000000000000000000)
  directionHi := (433188173419298022611/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree080.table
  base := (-1523812311179563367360455204518818960637/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-557694096653366014241584593478220000000000000)
      constant := (13647747349705804465821362154506519947255549335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree080.table
  base := (-1523819355709364170136805532210737110591/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-144890006729419718201970493930220000000000000)
      constant := (3579748839986684657893092284993481449968700405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree080.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel080

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43318817341929802261/10000000000000000000)
  centralHi := (433188173419298022611/100000000000000000000)
  directionLo := (54490156118067107557/12500000000000000000)
  directionHi := (435921248944536860457/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree081.table
  base := (-1909981134810626067642336537743942653471/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-564435662953733071323311767078220000000000000)
      constant := (13986843174590850747581191543725059468772454244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree081.table
  base := (-7639955682404431783143187672220074879841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-146642020175015530345161155530220000000000000)
      constant := (3668685400763908878357571376415637225599766831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree081.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel081

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54490156118067107557/12500000000000000000)
  centralHi := (435921248944536860457/100000000000000000000)
  directionLo := (438637295464466792143/100000000000000000000)
  directionHi := (27414830966529174509/6250000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree082.table
  base := (-7658701593330997262085783272211243689061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-571177229254100128405038940678220000000000000)
      constant := (14330109749938286226018389546135086858817485251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree082.table
  base := (-7658729135364514554214105456455450382189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-148394033620611342488351817130220000000000000)
      constant := (3758715705964195617465063103223304126895356899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree082.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel082

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438637295464466792143/100000000000000000000)
  centralHi := (27414830966529174509/6250000000000000000)
  directionLo := (55167078421968381307/12500000000000000000)
  directionHi := (441336627375747050457/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree083.table
  base := (-3837696721792712721005287898278154004681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-577918795554467185486766114278220000000000000)
      constant := (14677547045854190361183129908338371103242201342) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree083.table
  base := (-1535083561130100662914842296539250901203/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-150146047066207154631542478730220000000000000)
      constant := (3849839748498362462311030605571535435945686865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree083.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel083

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55167078421968381307/12500000000000000000)
  centralHi := (441336627375747050457/100000000000000000000)
  directionLo := (444019549518279726199/100000000000000000000)
  directionHi := (2220097747591398631/500000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree084.table
  base := (-3845000361995448163596274999316704639423/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (167649)
      previous := (0)
      next := (109040)
      square := (794737490693677460854016400000000000000000)
      linear := (-83522908836404891795499041125460000000000000)
      constant := (2147022148030381551059084192626285119575433598) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree084.table
  base := (-1538004455416610525888112772547249080119/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-151898060511802966774733140330220000000000000)
      constant := (3942057522172656088613086113952311172545087645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree084.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel084

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444019549518279726199/100000000000000000000)
  centralHi := (2220097747591398631/500000000000000000)
  directionLo := (111671589394257168763/25000000000000000000)
  directionHi := (446686357577028675053/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree085.table
  base := (-7702523989328241078501953291957012023549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-591401928155201299650220461478220000000000000)
      constant := (15384933698151764443401465840608443491521569259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree085.table
  base := (-7702543060415459862569679847315788048547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-153650073957398778917923801930220000000000000)
      constant := (4035369021568494764639136736852526804592964877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree085.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel085

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111671589394257168763/25000000000000000000)
  centralHi := (446686357577028675053/100000000000000000000)
  directionLo := (449337338462374150167/100000000000000000000)
  directionHi := (56167167307796768771/12500000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree086.table
  base := (-7712963725703177596678327172293642965371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-598143494455568356731947635078220000000000000)
      constant := (15744883011639540590175183619512671267040026461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree086.table
  base := (-385649030154248752097097498540621842797/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-155402087402994591061114463530220000000000000)
      constant := (4129774241939016704842338511092970857395332540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree086.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel086

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449337338462374150167/100000000000000000000)
  centralHi := (56167167307796768771/12500000000000000000)
  directionLo := (451972770670388112477/100000000000000000000)
  directionHi := (225986385335194056239/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree087.table
  base := (-772132035961890915962049448626574467689/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14210000000000000000000000000000000000000000
      center := (40467)
      previous := (0)
      next := (26320)
      square := (191833187408818697447521200000000000000000)
      linear := (-20858105543308117717712924437180000000000000)
      constant := (555482860658628579098476210152076376814139310) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree087.table
  base := (-3860667648805195488827053242601039647267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-157154100848590403204305125130220000000000000)
      constant := (4225273179119990036300375204212431140764288794) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree087.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel087

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451972770670388112477/100000000000000000000)
  centralHi := (225986385335194056239/50000000000000000000)
  directionLo := (454592924624310783803/100000000000000000000)
  directionHi := (113648231156077695951/25000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree088.table
  base := (-7727594265801852565016731199775711990663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-611626627056302470895401982278220000000000000)
      constant := (16477293525091728144627409101022202684576768433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree088.table
  base := (-1931901872207847483315203266535877788987/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-158906114294186215347495786730220000000000000)
      constant := (4321865829453010569879195389275843490146547668) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree088.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel088

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454592924624310783803/100000000000000000000)
  centralHi := (113648231156077695951/25000000000000000000)
  directionLo := (457198062998413595383/100000000000000000000)
  directionHi := (57149757874801699423/12500000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree089.table
  base := (-7731785773958732623624428313704870392721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-618368193356669527977129155878220000000000000)
      constant := (16849754696027154219763479313593315995986360311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree089.table
  base := (-3865898740077857095953110577021351628033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-160658127739782027490686448330220000000000000)
      constant := (4419552189719225567696922763651940961156395806) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree089.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel089

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457198062998413595383/100000000000000000000)
  centralHi := (57149757874801699423/12500000000000000000)
  directionLo := (114947110256336595451/25000000000000000000)
  directionHi := (91957688205069276361/20000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree090.table
  base := (-3866947587308367240614385170677209724123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-625109759657036585058856329478220000000000000)
      constant := (17226386459934172246591359063514925728957230586) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree090.table
  base := (-7733905538955425781716082490696128507583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-162410141185377839633877109930220000000000000)
      constant := (4518332257082084823697171227112004772663051953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree090.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel090

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114947110256336595451/25000000000000000000)
  centralHi := (91957688205069276361/20000000000000000000)
  directionLo := (28897769174249169071/6250000000000000000)
  directionHi := (462364306787986705137/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree091.table
  base := (-3866961362087988231832839387576175519891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (167649)
      previous := (0)
      next := (109040)
      square := (794737490693677460854016400000000000000000)
      linear := (-90264475136771948877226214725460000000000000)
      constant := (2515312686606684249860239408857938109428803366) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree091.table
  base := (-60421342978379504832549371685562047729/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-164162154630973651777067771530220000000000000)
      constant := (4618206029037842569104413117857267646162308992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree091.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel091

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28897769174249169071/6250000000000000000)
  centralHi := (462364306787986705137/100000000000000000000)
  directionLo := (464925901496735874987/100000000000000000000)
  directionHi := (116231475374183968747/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree092.table
  base := (-3865934324642295741634765819432967128683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-638592892257770699222310676678220000000000000)
      constant := (17992161725625063817870042325083813715188204506) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree092.table
  base := (-7731876775656901176870469414594664954869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-165914168076569463920258433130220000000000000)
      constant := (4719173503372721590879595221797605199493794779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree092.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel092

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (464925901496735874987/100000000000000000000)
  centralHi := (116231475374183968747/25000000000000000000)
  directionLo := (467473459753138938247/100000000000000000000)
  directionHi := (58434182469142367281/12500000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree093.table
  base := (-482983321914414505091615805132299246771/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-645334458558137756304037850278220000000000000)
      constant := (18381305209798840495956854036309709285437021776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree093.table
  base := (-1931935086765787573876108154691136131547/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-167666181522165276063449094730220000000000000)
      constant := (4821234678125810017373083109345186947121671508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree093.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel093

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (467473459753138938247/100000000000000000000)
  centralHi := (58434182469142367281/12500000000000000000)
  directionLo := (470007209800644091879/100000000000000000000)
  directionHi := (11750180245016102297/2500000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree094.table
  base := (-1930379101557845439233705261065306029367/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-652076024858504813385765023878220000000000000)
      constant := (18774619251432205547584999518254919215343261188) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree094.table
  base := (-3016219835735536653141157726813996947/3906250000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-169418194967761088206639756330220000000000000)
      constant := (4924389551556896075245883183429429584356549120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree094.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel094

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470007209800644091879/100000000000000000000)
  centralHi := (11750180245016102297/2500000000000000000)
  directionLo := (236263686881630062253/50000000000000000000)
  directionHi := (472527373763260124507/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree095.table
  base := (-482076160893067373942125094560198685703/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-658817591158871870467492197478220000000000000)
      constant := (19172103844005802968713238498859200357773841168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree095.table
  base := (-7713224218775470038280824536399843782947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-171170208413356900349830417930220000000000000)
      constant := (5028638122118560591144653894652234057306715277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree095.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel095

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236263686881630062253/50000000000000000000)
  centralHi := (472527373763260124507/100000000000000000000)
  directionLo := (475034167872818169207/100000000000000000000)
  directionHi := (59379270984102271151/12500000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree096.table
  base := (-7702839795672207884040363597944350149231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-665559157459238927549219371078220000000000000)
      constant := (19573758981714583273442186429838231274700339721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree096.table
  base := (-7702844794911348526283538911412525194653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-172922221858952712493021079530220000000000000)
      constant := (5133980388431944306795043021828344520209926323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree096.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel096

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (475034167872818169207/100000000000000000000)
  centralHi := (59379270984102271151/12500000000000000000)
  directionLo := (95505560537099169397/20000000000000000000)
  directionHi := (238763901342747923493/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree097.table
  base := (-3845190098036577971186590998619002104323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-672300723759605984630946544678220000000000000)
      constant := (19979584659378888989630882340160759084565906986) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree097.table
  base := (-7510141234333836539195192615088275267/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-174674235304548524636211741130220000000000000)
      constant := (5240416349265689880250254262103785171397014528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree097.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel097

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95505560537099169397/20000000000000000000)
  centralHi := (238763901342747923493/50000000000000000000)
  directionLo := (240004241644108717009/50000000000000000000)
  directionHi := (480008483288217434019/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree098.table
  base := (-7675839887885838002476880786563970919233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (167649)
      previous := (0)
      next := (109040)
      square := (794737490693677460854016400000000000000000)
      linear := (-97006041437139005958953388325460000000000000)
      constant := (2912797267481011319892466331155777903198475329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree098.table
  base := (-3837921904902451902391259285871563877269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-176426248750144336779402402730220000000000000)
      constant := (5347946003517629007041201515373137157652106358) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree098.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel098

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240004241644108717009/50000000000000000000)
  centralHi := (480008483288217434019/100000000000000000000)
  directionLo := (482476409495502667549/100000000000000000000)
  directionHi := (9649528189910053351/2000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree099.table
  base := (-1914804742960214303975733525650670985091/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-685783856360340098794400891878220000000000000)
      constant := (20803747616528146597019047665928825997501539924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree099.table
  base := (-3829611222833684157700959302772280013971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-178178262195740148922593064330220000000000000)
      constant := (5456569350198845298714184545195157762663563322) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree099.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel099

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (482476409495502667549/100000000000000000000)
  centralHi := (9649528189910053351/2000000000000000000)
  directionLo := (242465888018649459263/50000000000000000000)
  directionHi := (484931776037298918527/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree100.table
  base := (-7640517538430505774875958720640367108231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-692525422660707155876128065478220000000000000)
      constant := (21222084888132994193996848150983131111836908721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree100.table
  base := (-1528104123078654776818771896934155119903/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-179930275641335961065783725930220000000000000)
      constant := (5566286388419794986580920762789127741664745365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree100.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel100

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242465888018649459263/50000000000000000000)
  centralHi := (484931776037298918527/100000000000000000000)
  directionLo := (97474954547659287143/20000000000000000000)
  directionHi := (121843693184574108929/25000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree101.table
  base := (-1523947133830295390325662982017209466621/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-699266988961074212957855239078220000000000000)
      constant := (21644592683823224797125242438911284075450076055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree101.table
  base := (-1523947678920787713147547789108531041947/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-181682289086931773208974387530220000000000000)
      constant := (5677097117378211507397194637569357970879921385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree101.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel101

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97474954547659287143/20000000000000000000)
  centralHi := (121843693184574108929/25000000000000000000)
  directionLo := (244902792344596981517/50000000000000000000)
  directionHi := (97961116937838792607/20000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree102.table
  base := (-1899218359397332980778272255742884377761/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-706008555261441270039582412678220000000000000)
      constant := (22071271000566451015863170794232405910707387804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree102.table
  base := (-7596875851688198678987642340654361585591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-183434302532527585352165049130220000000000000)
      constant := (5789001536348557696658404978031237877938465081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree102.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel102

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244902792344596981517/50000000000000000000)
  centralHi := (97961116937838792607/20000000000000000000)
  directionLo := (123056098102588007361/25000000000000000000)
  directionHi := (98444878482070405889/20000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree103.table
  base := (-1892982727591372412092975041108186541157/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-712750121561808327121309586278220000000000000)
      constant := (22502119835617270796327487135242950963301844748) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree103.table
  base := (-378596652433499546668111591714519843199/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1030000000000000000000000000000000000000000
      center := (2961)
      previous := (0)
      next := (1880)
      square := (13904868615839778914211600000000000000000)
      linear := (-1797925397845858228110249618740000000000000)
      constant := (57300967424007976794303575701688089123010060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree103.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel103

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123056098102588007361/25000000000000000000)
  centralHi := (98444878482070405889/20000000000000000000)
  directionLo := (494631372008243409147/100000000000000000000)
  directionHi := (123657843002060852287/25000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree104.table
  base := (-301796325918587802196115704879897338859/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-719491687862175384203036759878220000000000000)
      constant := (22937139186483168284800920433998187764073986725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree104.table
  base := (-3772455020982949524035987539144529550903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-186938329423719209638546372330220000000000000)
      constant := (6016091441752479710184680743978911371988940146) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree104.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel104

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494631372008243409147/100000000000000000000)
  centralHi := (123657843002060852287/25000000000000000000)
  directionLo := (497026695325084467981/100000000000000000000)
  directionHi := (248513347662542233991/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree105.table
  base := (-7515805205458502803879999873940773826311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (167649)
      previous := (0)
      next := (109040)
      square := (794737490693677460854016400000000000000000)
      linear := (-103747607737506063040680561925460000000000000)
      constant := (3339475578699242826464450580827410664484507143) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree105.table
  base := (-3757903441523517090918647548615932557259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-188690342869315021781737033930220000000000000)
      constant := (6131276927041474979489777350278567143000078538) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree105.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel105

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (497026695325084467981/100000000000000000000)
  centralHi := (248513347662542233991/50000000000000000000)
  directionLo := (499410530082007185069/100000000000000000000)
  directionHi := (49941053008200718507/10000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree106.table
  base := (-3742311066569116608698525899676092498649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1173543)
      previous := (0)
      next := (763280)
      square := (5563162434855742225978114800000000000000000)
      linear := (-732974820462909498366491107078220000000000000)
      constant := (23819689426779410278525023395136615808446346718) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree106.table
  base := (-1496924723803537482817283951336384820991/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (304983)
      previous := (0)
      next := (193640)
      square := (1432201467431497228163794800000000000000000)
      linear := (-190442356314910833924927695530220000000000000)
      constant := (6247556100040077993666904046747081467170532405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree106.checked
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
end ForestUnimodality.Stage170KernelData.Cell296.Kernel106

namespace ForestUnimodality.Stage170KernelData.Cell296
open FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem degreePropagationThreshold : row.degreePropagationCheck 106 interval.lo interval.hi = true := by
  decide +kernel

theorem degreePropagationTail (n : ℕ) (hn : 106 ≤ n) (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual n j q :=
  row.degreePropagationCheck_sound 106 interval.lo interval.hi degreePropagationThreshold
    (fun _q hq j => Kernel106.actual_residual_nonneg j hq) n hn q hq j
end ForestUnimodality.Stage170KernelData.Cell296

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel107
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 107 j q :=
  degreePropagationTail 107 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel107

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel108
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 108 j q :=
  degreePropagationTail 108 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel108

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel109
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 109 j q :=
  degreePropagationTail 109 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel109

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel110
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 110 j q :=
  degreePropagationTail 110 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel110

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel111
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 111 j q :=
  degreePropagationTail 111 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel111

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel112
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 112 j q :=
  degreePropagationTail 112 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel112

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel113
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 113 j q :=
  degreePropagationTail 113 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel113

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel114
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 114 j q :=
  degreePropagationTail 114 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel114

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel115
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 115 j q :=
  degreePropagationTail 115 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel115

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel116
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 116 j q :=
  degreePropagationTail 116 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel116

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel117
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 117 j q :=
  degreePropagationTail 117 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel117

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel118
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 118 j q :=
  degreePropagationTail 118 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel118

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel119
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 119 j q :=
  degreePropagationTail 119 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel119

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel120
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 120 j q :=
  degreePropagationTail 120 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel120

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel121
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 121 j q :=
  degreePropagationTail 121 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel121

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel122
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 122 j q :=
  degreePropagationTail 122 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel122

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel123
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 123 j q :=
  degreePropagationTail 123 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel123

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel124
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 124 j q :=
  degreePropagationTail 124 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel124

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel125
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 125 j q :=
  degreePropagationTail 125 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel125

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel126
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 126 j q :=
  degreePropagationTail 126 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel126

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel127
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 127 j q :=
  degreePropagationTail 127 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel127

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel128
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 128 j q :=
  degreePropagationTail 128 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel128

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel129
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 129 j q :=
  degreePropagationTail 129 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel129

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel130
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  degreePropagationTail 130 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel130

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel131
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  degreePropagationTail 131 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel131

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel132
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  degreePropagationTail 132 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel132

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel133
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  degreePropagationTail 133 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel133

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel134
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  degreePropagationTail 134 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel134

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel135
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  degreePropagationTail 135 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel135

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel136
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  degreePropagationTail 136 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel136

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel137
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  degreePropagationTail 137 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel137

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel138
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  degreePropagationTail 138 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel138

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel139
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  degreePropagationTail 139 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel139

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel140
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  degreePropagationTail 140 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel140

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel141
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  degreePropagationTail 141 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel141

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel142
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  degreePropagationTail 142 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel142

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel143
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  degreePropagationTail 143 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel143

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel144
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  degreePropagationTail 144 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel144

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel145
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  degreePropagationTail 145 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel145

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel146
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  degreePropagationTail 146 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel146

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel147
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  degreePropagationTail 147 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel147

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel148
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  degreePropagationTail 148 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel148

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel149
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  degreePropagationTail 149 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel149

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel150
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  degreePropagationTail 150 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel150

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel151
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  degreePropagationTail 151 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel151

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel152
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  degreePropagationTail 152 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel152

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel153
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  degreePropagationTail 153 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel153

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel154
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  degreePropagationTail 154 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel154

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel155
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  degreePropagationTail 155 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel155

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel156
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  degreePropagationTail 156 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel156

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel157
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  degreePropagationTail 157 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel157

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel158
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  degreePropagationTail 158 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel158

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel159
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  degreePropagationTail 159 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel159

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel160
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  degreePropagationTail 160 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel160

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel161
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  degreePropagationTail 161 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel161

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel162
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  degreePropagationTail 162 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel162

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel163
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  degreePropagationTail 163 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel163

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel164
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  degreePropagationTail 164 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel164

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel165
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  degreePropagationTail 165 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel165

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel166
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  degreePropagationTail 166 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel166

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel167
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  degreePropagationTail 167 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel167

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel168
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  degreePropagationTail 168 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel168

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel169
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  degreePropagationTail 169 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel169

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel170
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 170 j q :=
  degreePropagationTail 170 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel170

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel171
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 171 j q :=
  degreePropagationTail 171 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel171

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel172
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 172 j q :=
  degreePropagationTail 172 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel172

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel173
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 173 j q :=
  degreePropagationTail 173 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel173

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel174
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 174 j q :=
  degreePropagationTail 174 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel174

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel175
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 175 j q :=
  degreePropagationTail 175 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel175

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel176
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 176 j q :=
  degreePropagationTail 176 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel176

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel177
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 177 j q :=
  degreePropagationTail 177 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel177

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel178
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 178 j q :=
  degreePropagationTail 178 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel178

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel179
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 179 j q :=
  degreePropagationTail 179 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel179

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel180
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 180 j q :=
  degreePropagationTail 180 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel180

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel181
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 181 j q :=
  degreePropagationTail 181 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel181

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel182
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 182 j q :=
  degreePropagationTail 182 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel182

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel183
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 183 j q :=
  degreePropagationTail 183 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel183

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel184
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 184 j q :=
  degreePropagationTail 184 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel184

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel185
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 185 j q :=
  degreePropagationTail 185 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel185

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel186
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 186 j q :=
  degreePropagationTail 186 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel186

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel187
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 187 j q :=
  degreePropagationTail 187 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel187

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel188
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 188 j q :=
  degreePropagationTail 188 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel188

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel189
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 189 j q :=
  degreePropagationTail 189 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel189

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel190
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 190 j q :=
  degreePropagationTail 190 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel190

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel191
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 191 j q :=
  degreePropagationTail 191 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel191

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel192
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 192 j q :=
  degreePropagationTail 192 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel192

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel193
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 193 j q :=
  degreePropagationTail 193 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel193

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel194
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 194 j q :=
  degreePropagationTail 194 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel194

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel195
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 195 j q :=
  degreePropagationTail 195 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel195

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel196
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 196 j q :=
  degreePropagationTail 196 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel196

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel197
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 197 j q :=
  degreePropagationTail 197 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel197

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel198
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 198 j q :=
  degreePropagationTail 198 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel198

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel199
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 199 j q :=
  degreePropagationTail 199 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel199

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel200
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 200 j q :=
  degreePropagationTail 200 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel200

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel201
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 201 j q :=
  degreePropagationTail 201 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel201

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel202
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 202 j q :=
  degreePropagationTail 202 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel202

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel203
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 203 j q :=
  degreePropagationTail 203 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel203

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel204
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 204 j q :=
  degreePropagationTail 204 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel204

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel205
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 205 j q :=
  degreePropagationTail 205 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel205

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel206
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 206 j q :=
  degreePropagationTail 206 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel206

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel207
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 207 j q :=
  degreePropagationTail 207 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel207

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel208
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 208 j q :=
  degreePropagationTail 208 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel208

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel209
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 209 j q :=
  degreePropagationTail 209 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel209

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel210
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 210 j q :=
  degreePropagationTail 210 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel210

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel211
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 211 j q :=
  degreePropagationTail 211 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel211

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel212
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 212 j q :=
  degreePropagationTail 212 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel212

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel213
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 213 j q :=
  degreePropagationTail 213 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel213

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel214
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 214 j q :=
  degreePropagationTail 214 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel214

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel215
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 215 j q :=
  degreePropagationTail 215 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel215

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel216
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 216 j q :=
  degreePropagationTail 216 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel216

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel217
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 217 j q :=
  degreePropagationTail 217 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel217

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel218
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 218 j q :=
  degreePropagationTail 218 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel218

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel219
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 219 j q :=
  degreePropagationTail 219 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel219

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel220
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 220 j q :=
  degreePropagationTail 220 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel220

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel221
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 221 j q :=
  degreePropagationTail 221 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel221

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel222
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 222 j q :=
  degreePropagationTail 222 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel222

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel223
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 223 j q :=
  degreePropagationTail 223 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel223

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel224
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 224 j q :=
  degreePropagationTail 224 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel224

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel225
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 225 j q :=
  degreePropagationTail 225 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel225

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel226
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 226 j q :=
  degreePropagationTail 226 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel226

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel227
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 227 j q :=
  degreePropagationTail 227 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel227

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel228
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 228 j q :=
  degreePropagationTail 228 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel228

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel229
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 229 j q :=
  degreePropagationTail 229 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel229

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel230
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 230 j q :=
  degreePropagationTail 230 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel230

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel231
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 231 j q :=
  degreePropagationTail 231 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel231

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel232
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 232 j q :=
  degreePropagationTail 232 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel232

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel233
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 233 j q :=
  degreePropagationTail 233 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel233

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel234
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 234 j q :=
  degreePropagationTail 234 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel234

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel235
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 235 j q :=
  degreePropagationTail 235 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel235

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel236
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 236 j q :=
  degreePropagationTail 236 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel236

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel237
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 237 j q :=
  degreePropagationTail 237 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel237

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel238
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 238 j q :=
  degreePropagationTail 238 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel238

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel239
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 239 j q :=
  degreePropagationTail 239 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel239

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel240
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 240 j q :=
  degreePropagationTail 240 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel240

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel241
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 241 j q :=
  degreePropagationTail 241 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel241

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel242
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 242 j q :=
  degreePropagationTail 242 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel242

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel243
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 243 j q :=
  degreePropagationTail 243 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel243

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel244
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 244 j q :=
  degreePropagationTail 244 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel244

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel245
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 245 j q :=
  degreePropagationTail 245 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel245

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel246
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 246 j q :=
  degreePropagationTail 246 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel246

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel247
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 247 j q :=
  degreePropagationTail 247 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel247

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel248
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 248 j q :=
  degreePropagationTail 248 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel248

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel249
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 249 j q :=
  degreePropagationTail 249 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel249

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel250
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 250 j q :=
  degreePropagationTail 250 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel250

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel251
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 251 j q :=
  degreePropagationTail 251 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel251

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel252
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 252 j q :=
  degreePropagationTail 252 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel252

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel253
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 253 j q :=
  degreePropagationTail 253 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel253

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel254
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 254 j q :=
  degreePropagationTail 254 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel254

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel255
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 255 j q :=
  degreePropagationTail 255 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel255

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel256
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 256 j q :=
  degreePropagationTail 256 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel256

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel257
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 257 j q :=
  degreePropagationTail 257 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel257

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel258
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 258 j q :=
  degreePropagationTail 258 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel258

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel259
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 259 j q :=
  degreePropagationTail 259 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel259

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel260
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 260 j q :=
  degreePropagationTail 260 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel260

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel261
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 261 j q :=
  degreePropagationTail 261 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel261

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel262
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 262 j q :=
  degreePropagationTail 262 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel262

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel263
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 263 j q :=
  degreePropagationTail 263 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel263

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel264
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 264 j q :=
  degreePropagationTail 264 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel264

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel265
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 265 j q :=
  degreePropagationTail 265 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel265

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel266
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 266 j q :=
  degreePropagationTail 266 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel266

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel267
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 267 j q :=
  degreePropagationTail 267 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel267

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel268
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 268 j q :=
  degreePropagationTail 268 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel268

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel269
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 269 j q :=
  degreePropagationTail 269 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel269

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel270
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 270 j q :=
  degreePropagationTail 270 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel270

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel271
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 271 j q :=
  degreePropagationTail 271 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel271

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel272
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 272 j q :=
  degreePropagationTail 272 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel272

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel273
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 273 j q :=
  degreePropagationTail 273 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel273

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel274
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 274 j q :=
  degreePropagationTail 274 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel274

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel275
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 275 j q :=
  degreePropagationTail 275 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel275

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel276
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 276 j q :=
  degreePropagationTail 276 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel276

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel277
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 277 j q :=
  degreePropagationTail 277 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel277

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel278
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 278 j q :=
  degreePropagationTail 278 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel278

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel279
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 279 j q :=
  degreePropagationTail 279 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel279

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel280
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 280 j q :=
  degreePropagationTail 280 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel280

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel281
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 281 j q :=
  degreePropagationTail 281 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel281

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel282
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 282 j q :=
  degreePropagationTail 282 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel282

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel283
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 283 j q :=
  degreePropagationTail 283 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel283

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel284
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 284 j q :=
  degreePropagationTail 284 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel284

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel285
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 285 j q :=
  degreePropagationTail 285 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel285

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel286
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 286 j q :=
  degreePropagationTail 286 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel286

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel287
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 287 j q :=
  degreePropagationTail 287 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel287

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel288
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 288 j q :=
  degreePropagationTail 288 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel288

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel289
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 289 j q :=
  degreePropagationTail 289 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel289

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel290
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 290 j q :=
  degreePropagationTail 290 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel290

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel291
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 291 j q :=
  degreePropagationTail 291 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel291

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel292
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 292 j q :=
  degreePropagationTail 292 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel292

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel293
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 293 j q :=
  degreePropagationTail 293 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel293

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel294
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 294 j q :=
  degreePropagationTail 294 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel294

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel295
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 295 j q :=
  degreePropagationTail 295 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel295

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel296
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 296 j q :=
  degreePropagationTail 296 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel296

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel297
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 297 j q :=
  degreePropagationTail 297 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel297

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel298
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 298 j q :=
  degreePropagationTail 298 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel298

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel299
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 299 j q :=
  degreePropagationTail 299 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel299

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel300
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 300 j q :=
  degreePropagationTail 300 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel300

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel301
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 301 j q :=
  degreePropagationTail 301 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel301

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel302
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 302 j q :=
  degreePropagationTail 302 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel302

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel303
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 303 j q :=
  degreePropagationTail 303 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel303

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel304
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 304 j q :=
  degreePropagationTail 304 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel304

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel305
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 305 j q :=
  degreePropagationTail 305 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel305

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel306
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 306 j q :=
  degreePropagationTail 306 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel306

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel307
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 307 j q :=
  degreePropagationTail 307 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel307

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel308
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 308 j q :=
  degreePropagationTail 308 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel308

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel309
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 309 j q :=
  degreePropagationTail 309 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel309

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel310
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 310 j q :=
  degreePropagationTail 310 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel310

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel311
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 311 j q :=
  degreePropagationTail 311 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel311

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel312
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 312 j q :=
  degreePropagationTail 312 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel312

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel313
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 313 j q :=
  degreePropagationTail 313 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel313

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel314
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 314 j q :=
  degreePropagationTail 314 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel314

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel315
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 315 j q :=
  degreePropagationTail 315 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel315

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel316
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 316 j q :=
  degreePropagationTail 316 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel316

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel317
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 317 j q :=
  degreePropagationTail 317 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel317

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel318
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 318 j q :=
  degreePropagationTail 318 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel318

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel319
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 319 j q :=
  degreePropagationTail 319 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel319

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel320
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 320 j q :=
  degreePropagationTail 320 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel320

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel321
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 321 j q :=
  degreePropagationTail 321 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel321

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel322
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 322 j q :=
  degreePropagationTail 322 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel322

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel323
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 323 j q :=
  degreePropagationTail 323 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel323

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel324
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 324 j q :=
  degreePropagationTail 324 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel324

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel325
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 325 j q :=
  degreePropagationTail 325 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel325

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel326
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 326 j q :=
  degreePropagationTail 326 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel326

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel327
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 327 j q :=
  degreePropagationTail 327 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel327

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel328
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 328 j q :=
  degreePropagationTail 328 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel328

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel329
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 329 j q :=
  degreePropagationTail 329 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel329

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel330
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 330 j q :=
  degreePropagationTail 330 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel330

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel331
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 331 j q :=
  degreePropagationTail 331 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel331

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel332
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 332 j q :=
  degreePropagationTail 332 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel332

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel333
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 333 j q :=
  degreePropagationTail 333 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel333

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel334
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 334 j q :=
  degreePropagationTail 334 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel334

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel335
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 335 j q :=
  degreePropagationTail 335 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel335

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel336
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 336 j q :=
  degreePropagationTail 336 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel336

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel337
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 337 j q :=
  degreePropagationTail 337 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel337

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel338
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 338 j q :=
  degreePropagationTail 338 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel338

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel339
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 339 j q :=
  degreePropagationTail 339 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel339

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel340
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 340 j q :=
  degreePropagationTail 340 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel340

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel341
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 341 j q :=
  degreePropagationTail 341 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel341

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel342
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 342 j q :=
  degreePropagationTail 342 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel342

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel343
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 343 j q :=
  degreePropagationTail 343 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel343

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel344
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 344 j q :=
  degreePropagationTail 344 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel344

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel345
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 345 j q :=
  degreePropagationTail 345 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel345

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel346
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 346 j q :=
  degreePropagationTail 346 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel346

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel347
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 347 j q :=
  degreePropagationTail 347 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel347

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel348
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 348 j q :=
  degreePropagationTail 348 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel348

namespace ForestUnimodality.Stage170KernelData.Cell296.Kernel349
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 106 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 349 j q :=
  degreePropagationTail 349 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell296.Kernel349

