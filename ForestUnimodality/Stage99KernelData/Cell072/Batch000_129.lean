import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell072.Parameters
import ForestUnimodality.BinomialMassData.Q5227_10302.Batch000_049
import ForestUnimodality.BinomialMassData.Q5227_10302.Batch050_099
import ForestUnimodality.BinomialMassData.Q5227_10302.Batch100_149
import ForestUnimodality.BinomialMassData.Q3493_6868.Batch000_049
import ForestUnimodality.BinomialMassData.Q3493_6868.Batch050_099
import ForestUnimodality.BinomialMassData.Q3493_6868.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree000.table
  base := (5091015259829945509672199979/100000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (102)
      previous := (51)
      next := (51)
      square := (909981180403976186443770760000000000000)
      linear := (-11407163399013036698959045000000000000)
      constant := (509101525982994550967219997900000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree000.table
  base := (5091015259829945509672199979/100000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (102)
      previous := (51)
      next := (51)
      square := (909981180403976186443770760000000000000)
      linear := (-11407163399013036698959045000000000000)
      constant := (509101525982994550967219997900000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree001.table
  base := (71446482793158870415547971577246290175649/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-24803249362424123244354906114875565000000000000)
      constant := (7589070324519268891518741735142718523374999851396) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree001.table
  base := (17828389126318158380015218066373126125741/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-2762426752853042695673283822742785000000000000)
      constant := (841665869808427312630531623747475992180554543184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (12498154918677782967/25000000000000000000)
  directionHi := (49992619674711131869/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree002.table
  base := (84433126907940014493243132326455074091593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-49303834728407749989570634981616085000000000000)
      constant := (4505663914949236204592598577896926537624985683986) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree002.table
  base := (21039022596640629507441894520599984996519/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-5491224172768252446997770173470565000000000000)
      constant := (499009177068932840796304489495693345847221617528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498154918677782967/25000000000000000000)
  centralHi := (49992619674711131869/100000000000000000000)
  directionLo := (70700240762536509997/100000000000000000000)
  directionHi := (35350120381268254999/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree003.table
  base := (52947965635424538453048613077324163285453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-8200491121599041859420707094261845000000000000)
      constant := (318457337698001432481443144269076617932095698634) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree003.table
  base := (52725829367943452688591518362646736125573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-8220021592683462198322256524198345000000000000)
      constant := (317177468631626746766948784068542013565408759994) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70700240762536509997/100000000000000000000)
  centralHi := (35350120381268254999/50000000000000000000)
  directionLo := (4329487864003357981/5000000000000000000)
  directionHi := (86589757280067159621/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree004.table
  base := (7058827409678720580777865090344883807169/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-98305005460375003480002092715097125000000000000)
      constant := (1972967197637234116470154633102917324237374503690) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree004.table
  base := (14051988152601682077942757022613633494971/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-10948819012598671949646742874926125000000000000)
      constant := (218303697721012930929388815419892905782777802095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4329487864003357981/5000000000000000000)
  centralHi := (86589757280067159621/100000000000000000000)
  directionLo := (12498154918677782967/12500000000000000000)
  directionHi := (99985239349422263737/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree005.table
  base := (2485903595165794153880646940682960865651/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-122805590826358630225217821581837645000000000000)
      constant := (1475315514543853956487012068470410007282114369020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree005.table
  base := (49479473656764461797458951587040238992261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-13677616432513881700971229225653905000000000000)
      constant := (163303417587963232495254323221004239880455739229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498154918677782967/12500000000000000000)
  centralHi := (99985239349422263737/100000000000000000000)
  directionLo := (22357379193189502981/20000000000000000000)
  directionHi := (55893447982973757453/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree006.table
  base := (36572779471185530079941530848030041960631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-16367352910260250774492616716508685000000000000)
      constant := (132784262610669108123308950404675233373674684159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree006.table
  base := (36396526463742001709741579170211975937109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-16406413852429091452295715576381685000000000000)
      constant := (132383951859761103040677368054515811428455734701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22357379193189502981/20000000000000000000)
  centralHi := (55893447982973757453/50000000000000000000)
  directionLo := (30614102277016354781/25000000000000000000)
  directionHi := (979651272864523353/800000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree007.table
  base := (27717239967986890171398120938671825664787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-171806761558325883715649279315318685000000000000)
      constant := (1041051411855633009262093919613514372170486178387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree007.table
  base := (5516527088118271283802886977755988730279/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-19135211272344301203620201927109465000000000000)
      constant := (115437884287738546354848735409920426549297434155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30614102277016354781/25000000000000000000)
  centralHi := (979651272864523353/800000000000000000)
  directionLo := (132268039047920423511/100000000000000000000)
  directionHi := (16533504880990052939/12500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree008.table
  base := (4272518313843470860005015653722305896239/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-196307346924309510460865008182059205000000000000)
      constant := (965831144816662414987561687486508758030180177195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree008.table
  base := (10627902448168612903599636664475303861319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-21864008692259510954944688277837245000000000000)
      constant := (107211732977283880887963248843512918170424138782) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132268039047920423511/100000000000000000000)
  centralHi := (16533504880990052939/12500000000000000000)
  directionLo := (70700240762536509997/50000000000000000000)
  directionHi := (28280096305014603999/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree009.table
  base := (4138512981972891392677243935561796614389/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-24534214698921459689564526338755525000000000000)
      constant := (104896056929803862874906824856160588176469810484) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree009.table
  base := (3293274437059461613798804877742837591749/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-24592806112174720706269174628565025000000000000)
      constant := (104905807928950215193129733810329375415108588305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70700240762536509997/50000000000000000000)
  centralHi := (28280096305014603999/20000000000000000000)
  directionLo := (37494464756033348901/25000000000000000000)
  directionHi := (29995571804826679121/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree010.table
  base := (1276407258690781008109078493714762572849/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-245308517656276763951296465915540245000000000000)
      constant := (961754176280213250191667596584613786076505200490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree010.table
  base := (12690149980620194078659120367071478405941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-27321603532089930457593660979292805000000000000)
      constant := (106974758250507505392255753906298750202292196749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37494464756033348901/25000000000000000000)
  centralHi := (29995571804826679121/20000000000000000000)
  directionLo := (31618108874126640633/20000000000000000000)
  directionHi := (79045272185316601583/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree011.table
  base := (2421881123909278650684268016241338625713/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-269809103022260390696512194782280765000000000000)
      constant := (1010804208172940396435728365671114090418626048452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree011.table
  base := (1203008514483383195095648525103894401931/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-30050400952005140208918147330020585000000000000)
      constant := (112525106118049302154549004126930395797954878872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31618108874126640633/20000000000000000000)
  centralHi := (79045272185316601583/50000000000000000000)
  directionLo := (165806761747956045531/100000000000000000000)
  directionHi := (41451690436989011383/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree012.table
  base := (285516030352092122088849709569875731729/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-32701076487582668604636435961002365000000000000)
      constant := (120696228634322116860314056000162104401930397025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree012.table
  base := (27667299307242970545260119908220340039/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-32779198371920349960242633680748365000000000000)
      constant := (121010576629261206708467346444109075875580280576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165806761747956045531/100000000000000000000)
  centralHi := (41451690436989011383/25000000000000000000)
  directionLo := (173179514560134319241/100000000000000000000)
  directionHi := (86589757280067159621/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree013.table
  base := (4994156843251799859940005775448896570847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-318810273754227644186943652515761805000000000000)
      constant := (1184928074377840558688216237631105470883865852447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree013.table
  base := (1236519902665972015204634907178416575279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-35507995791835559711567120031476145000000000000)
      constant := (132076361700168369591986692043269662521990767324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173179514560134319241/100000000000000000000)
  centralHi := (86589757280067159621/50000000000000000000)
  directionLo := (180250953631940847027/100000000000000000000)
  directionHi := (45062738407985211757/25000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree014.table
  base := (3173041476357150056324854887656926506279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-343310859120211270932159381382502325000000000000)
      constant := (1304581368730117374626875333408636802262725957479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree014.table
  base := (782740945099291465432577202045524138309/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-38236793211750769462891606382203925000000000000)
      constant := (145478190637548193939394117083793196345532966004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180250953631940847027/100000000000000000000)
  centralHi := (45062738407985211757/25000000000000000000)
  directionLo := (18705525469006318131/10000000000000000000)
  directionHi := (187055254690063181311/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree015.table
  base := (403586544977990921774111136065426156469/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-40867938276243877519708345583249205000000000000)
      constant := (160403160132774057552612313103736082028794150964) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree015.table
  base := (63100005977240576090633139541848434511/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-40965590631665979214216092732931705000000000000)
      constant := (161039234166910182733712382963192691486227486975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18705525469006318131/10000000000000000000)
  centralHi := (187055254690063181311/100000000000000000000)
  directionLo := (9681029171671873227/5000000000000000000)
  directionHi := (193620583433437464541/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree016.table
  base := (136385646913004630288761341786077833051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-392312029852178524422590839115983365000000000000)
      constant := (1600867364905846234515517006026380255429706811702) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree016.table
  base := (48105301623745583487245349936412383927/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-43694388051581188965540579083659485000000000000)
      constant := (178626350074779188822941211251341860242594827515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9681029171671873227/5000000000000000000)
  centralHi := (193620583433437464541/100000000000000000000)
  directionLo := (12498154918677782967/6250000000000000000)
  directionHi := (199970478698844527473/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree017.table
  base := (-886764220165529109016890025045905546771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 918090000000000000000000000000000000000000000
      center := (9364518)
      previous := (4682259)
      next := (4682259)
      square := (83544462191708649701216149704840000000000000)
      linear := (-1442258184145889796428396429005965000000000000)
      constant := (6143139590503815844476547793488142957656501261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree017.table
  base := (-228737077902879442153894697914934662863/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1040502)
      previous := (520251)
      next := (520251)
      square := (9282718021300961077912905522760000000000000)
      linear := (-160633859762963317359394690084385000000000000)
      constant := (685593014821679986658485369557402756016538148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498154918677782967/6250000000000000000)
  centralHi := (199970478698844527473/100000000000000000000)
  directionLo := (20612485142016560701/10000000000000000000)
  directionHi := (206124851420165607011/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree018.table
  base := (-1891977308481234918731920869581646931223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-49034800064905086434780255205496045000000000000)
      constant := (218488107024509356995460476272979737080177717153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree018.table
  base := (-958288112746282999555831892857907821007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-49151982891411608468189551785115045000000000000)
      constant := (219487807484368242298919338833804859279750588754) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20612485142016560701/10000000000000000000)
  centralHi := (206124851420165607011/100000000000000000000)
  directionLo := (26512590285951191249/12500000000000000000)
  directionHi := (212100722287609529993/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree019.table
  base := (-2765063437963758414168940881093661326537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-465813785950129404658238025716204925000000000000)
      constant := (2173355321695952398952640625548370749161597759863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree019.table
  base := (-2786500789564078882726228347455640779177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-51880780311326818219514038135842825000000000000)
      constant := (242615347503505955860493198403748013680956857247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26512590285951191249/12500000000000000000)
  centralHi := (212100722287609529993/100000000000000000000)
  directionLo := (43582555416985808759/20000000000000000000)
  directionHi := (54478194271232260949/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree020.table
  base := (-352395611259628010635191021623172146927/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-490314371316113031403453754582945445000000000000)
      constant := (2395778590989288901188134288524415414368431474730) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree020.table
  base := (-354261093865789817957222456345346952321/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-54609577731242027970838524486570605000000000000)
      constant := (267466263168879187286294217707962249486789354310) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43582555416985808759/20000000000000000000)
  centralHi := (54478194271232260949/25000000000000000000)
  directionLo := (22357379193189502981/10000000000000000000)
  directionHi := (223573791931895029811/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree021.table
  base := (-4183231907195074050751860435141696053109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-57201661853566295349852164827742885000000000000)
      constant := (292586223749081323176705492637209084924485941299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree021.table
  base := (-839888664729560641811048945412846025819/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-57338375151157237722163010837298385000000000000)
      constant := (293997699139950107376355283567923129612946450545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22357379193189502981/10000000000000000000)
  centralHi := (223573791931895029811/100000000000000000000)
  directionLo := (28636870481062795661/12500000000000000000)
  directionHi := (229094963848502365289/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree022.table
  base := (-4754787047425943132395995957956842025157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-539315542048080284893885212316426485000000000000)
      constant := (2885531949765039580705633366714053698958072325243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree022.table
  base := (-4768857718784543548114463642021950591701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-60067172571072447473487497188026165000000000000)
      constant := (322174691746707598061147361075665207202062790611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28636870481062795661/12500000000000000000)
  centralHi := (229094963848502365289/100000000000000000000)
  directionLo := (58621542799280986809/25000000000000000000)
  directionHi := (234486171197123947237/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree023.table
  base := (-131208953635849917623696468057859181771/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-563816127414063911639100941183167005000000000000)
      constant := (3152288059466751547929992708275448771261889177160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree023.table
  base := (-5260557288036116858495753218678121240073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-62795969990987657224811983538753945000000000000)
      constant := (351968635198192409082051724456872267481474429503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58621542799280986809/25000000000000000000)
  centralHi := (234486171197123947237/100000000000000000000)
  directionLo := (239756181368963321239/100000000000000000000)
  directionHi := (5993904534224083031/2500000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree024.table
  base := (-5671931210041574770735937468112229516337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-65368523642227504264924074449989725000000000000)
      constant := (381481383518222268736367347783623745397411570007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree024.table
  base := (-2841248707458965864287695365199245750131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-65524767410902866976136469889481725000000000000)
      constant := (383356076315771983049170742820984751591484100682) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239756181368963321239/100000000000000000000)
  centralHi := (5993904534224083031/2500000000000000000)
  directionLo := (244912818216130838249/100000000000000000000)
  directionHi := (979651272864523353/400000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree025.table
  base := (-301603366908094553025168372837325892287/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-612817298146031165129532398916648045000000000000)
      constant := (3728491042078046178609298442038843097056031882260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree025.table
  base := (-1510302826215512206429971372578018107093/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-68253564830818076727460956240209505000000000000)
      constant := (416317754628377321661708551093569466456713218892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244912818216130838249/100000000000000000000)
  centralHi := (979651272864523353/400000000000000000)
  directionLo := (12498154918677782967/5000000000000000000)
  directionHi := (249963098373555659341/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree026.table
  base := (-98971319361426148700476419043821704049/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-637317883512014791874748127783388565000000000000)
      constant := (4037620609054651996504745999971346585607167280064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree026.table
  base := (-6342071626258051741038007118817397694001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-70982362250733286478785442590937285000000000000)
      constant := (450837831031428445820136887753195319349690285911) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498154918677782967/5000000000000000000)
  centralHi := (249963098373555659341/100000000000000000000)
  directionLo := (25491334325697464059/10000000000000000000)
  directionHi := (254913343256974640591/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree027.table
  base := (-6582668841447597233529122322179459883963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-73535385430888713179995984072236565000000000000)
      constant := (484511464338289235947409287907195285790147403293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree027.table
  base := (-1647375502356290008697181779908324919887/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-73711159670648496230109928941665065000000000000)
      constant := (486903264269041197850271441758435361431021016228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25491334325697464059/10000000000000000000)
  centralHi := (254913343256974640591/100000000000000000000)
  directionLo := (129884635920100739431/50000000000000000000)
  directionHi := (259769271840201478863/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree028.table
  base := (-1356249417978150389113977385817794726489/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-686319054243982045365179585516869605000000000000)
      constant := (4697341468344897156535192882650917501316089671555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree028.table
  base := (-6787148706791642952239879393520280319593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-76439957090563705981434415292392845000000000000)
      constant := (524503304864540573901099809932630465312891392223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129884635920100739431/50000000000000000000)
  centralHi := (259769271840201478863/100000000000000000000)
  directionLo := (264536078095840847023/100000000000000000000)
  directionHi := (16533504880990052939/6250000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree029.table
  base := (-3466462915115761824049191517279218240171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-710819639609965672110395314383610125000000000000)
      constant := (5047755171565600339107488746188700534495945302058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree029.table
  base := (-6938020317161448009451610769187913865509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-79168754510478915732758901643120625000000000000)
      constant := (563629083200887243143947750071677050950145437699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264536078095840847023/100000000000000000000)
  centralHi := (16533504880990052939/6250000000000000000)
  directionLo := (53843699217742876821/20000000000000000000)
  directionHi := (134609248044357192053/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree030.table
  base := (-704020595543399127250136463975329044893/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-81702247219549922095067893694483405000000000000)
      constant := (601308659223486051645421531536581136713704405230) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree030.table
  base := (-7044601756680171182633159040763559108599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-81897551930394125484083387993848405000000000000)
      constant := (604273273524126451682908546536323987291089482689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53843699217742876821/20000000000000000000)
  centralHi := (134609248044357192053/50000000000000000000)
  directionLo := (273820855046158667657/100000000000000000000)
  directionHi := (136910427523079333829/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree031.table
  base := (-7105155906543299289751568598729689733977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-759820810341932925600826772117091165000000000000)
      constant := (5789354871147588483374538092198468606996645320423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree031.table
  base := (-7108947378149741804197792109542904676431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-84626349350309335235407874344576185000000000000)
      constant := (646429819419360712474317300772708368945365209641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273820855046158667657/100000000000000000000)
  centralHi := (136910427523079333829/50000000000000000000)
  directionLo := (278347126229371642933/100000000000000000000)
  directionHi := (139173563114685821467/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree032.table
  base := (-111398250655468065141372063901046874179/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-784321395707916552346042500983831685000000000000)
      constant := (6180440552309826353302654825672401014127139495744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree032.table
  base := (-7132757159341461641916254977525520183943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-87355146770224544986732360695303965000000000000)
      constant := (690093709200822206260928524918630286726439665073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278347126229371642933/100000000000000000000)
  centralHi := (139173563114685821467/50000000000000000000)
  directionLo := (282800963050146039989/100000000000000000000)
  directionHi := (28280096305014603999/10000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree033.table
  base := (-1778655306098580820551873328164507961331/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-89869109008211131010139803316730245000000000000)
      constant := (731666370010594639071847327718911858055150614164) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree033.table
  base := (-7117439114848320195666572211522160996689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-90083944190139754738056847046031745000000000000)
      constant := (735260791916177501221036313406945187659432122679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282800963050146039989/100000000000000000000)
  centralHi := (28280096305014603999/10000000000000000000)
  directionLo := (57437147117185540227/20000000000000000000)
  directionHi := (17949108474120481321/6250000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree034.table
  base := (-7061732170489372914477719440260197018071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 918090000000000000000000000000000000000000000
      center := (9364518)
      previous := (4682259)
      next := (4682259)
      square := (83544462191708649701216149704840000000000000)
      linear := (-2883469088027279604970498127049525000000000000)
      constant := (24231813089676260521603718799850336571967919561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree034.table
  base := (-3532080239894251194433447053778091677643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1040502)
      previous := (520251)
      next := (520251)
      square := (9282718021300961077912905522760000000000000)
      linear := (-321151355052093302731423298950725000000000000)
      constant := (2705631925440879801667632439271971873592727514) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57437147117185540227/20000000000000000000)
  centralHi := (17949108474120481321/6250000000000000000)
  directionLo := (14575228021026866161/5000000000000000000)
  directionHi := (291504560420537323221/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree035.table
  base := (-348589881248030867482192547657174915037/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-857823151805867432581689687584053245000000000000)
      constant := (7434404594999659153544468680385141122642627427260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree035.table
  base := (-3486944864868160986329534432873433369383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-95541539029970174240705819747487305000000000000)
      constant := (830091357657345087591366889428152891632978081826) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14575228021026866161/5000000000000000000)
  centralHi := (291504560420537323221/100000000000000000000)
  directionLo := (295760326561746630539/100000000000000000000)
  directionHi := (14788016328087331527/5000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree036.table
  base := (-1369125806855687841771109369607147782447/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-98035970796872339925211712938977085000000000000)
      constant := (875467515155254502840976166419705536505968031085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree036.table
  base := (-3423715556342964884100458658728432916927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-98270336449885383992030306098215085000000000000)
      constant := (879749614536305147849103317985693150860739194994) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295760326561746630539/100000000000000000000)
  centralHi := (14788016328087331527/5000000000000000000)
  directionLo := (37494464756033348901/12500000000000000000)
  directionHi := (299955718048266791209/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree037.table
  base := (-6683901081895071170530777028055365429489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-906824322537834686072121145317534285000000000000)
      constant := (8337385205867557324154264195069942364577088831311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree037.table
  base := (-6685453055621192360022879539235130902041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-100999133869800593743354792448942865000000000000)
      constant := (930900426507056003199833300067387530924132850351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37494464756033348901/12500000000000000000)
  centralHi := (299955718048266791209/100000000000000000000)
  directionLo := (4751456777324725703/1562500000000000000)
  directionHi := (304093233748782444993/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree038.table
  base := (-6487175194640214457326865173307441078967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-931324907903818312817336874184274805000000000000)
      constant := (8808922407184111025870681311866103429032543303433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree038.table
  base := (-6488511555067529532726247516779160385851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-103727931289715803494679278799670645000000000000)
      constant := (983542154442357025356191397384413079337236911261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4751456777324725703/1562500000000000000)
  centralHi := (304093233748782444993/100000000000000000000)
  directionLo := (308175204767891657743/100000000000000000000)
  directionHi := (19260950297993228609/6250000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree039.table
  base := (-6255918925104965974806265992245577393723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-106202832585533548840283622561223925000000000000)
      constant := (1032645203874121669127892493812768925486916554653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree039.table
  base := (-312853472795888926440849850946878285737/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-106456728709631013246003765150398425000000000000)
      constant := (1037673433834270934664755410338360662079597868140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308175204767891657743/100000000000000000000)
  centralHi := (19260950297993228609/6250000000000000000)
  directionLo := (19512738112703962483/6250000000000000000)
  directionHi := (312203809803263399729/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree040.table
  base := (-5990521948693268985568312661922432981431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-980326078635785566307768331917755845000000000000)
      constant := (9792028149736561891793478742496957108267854581769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree040.table
  base := (-5991512356450269440963885802979392619721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-109185526129546222997328251501126205000000000000)
      constant := (1093293127904754967240959593541360735391119336831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19512738112703962483/6250000000000000000)
  centralHi := (312203809803263399729/100000000000000000000)
  directionLo := (31618108874126640633/10000000000000000000)
  directionHi := (316181088741266406331/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree041.table
  base := (-1138261855799549683436588505919423790861/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-1004826664001769193052984060784496365000000000000)
      constant := (10303577728271536222527167645194919875112097341695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree041.table
  base := (-1138432348462248559358661933306778693937/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-111914323549461432748652737851853985000000000000)
      constant := (1150400288885511783493954373432776274284849818035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31618108874126640633/10000000000000000000)
  centralHi := (316181088741266406331/100000000000000000000)
  directionLo := (160054477365952572099/50000000000000000000)
  directionHi := (320108954731905144199/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree042.table
  base := (-5358552195304814032759052110282269802079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-114369694374194757755355532183470765000000000000)
      constant := (1203160930296966253567008184427376098501458722969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree042.table
  base := (-2679642921164588981785134074628422148387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-114643120969376642499977224202581765000000000000)
      constant := (1208994126014082660514378844784743021653967835114) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160054477365952572099/50000000000000000000)
  centralHi := (320108954731905144199/100000000000000000000)
  directionLo := (323989204945925955097/100000000000000000000)
  directionHi := (161994602472962977549/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree043.table
  base := (-4992477286566461159717397776059324831243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-1053827834733736446543415518517977405000000000000)
      constant := (11366634070900469979945812014361433357558270898357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree043.table
  base := (-1248277152389434509595088280724460764027/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-117371918389291852251301710553309545000000000000)
      constant := (1269073979056933577716009042141666577012561622388) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323989204945925955097/100000000000000000000)
  centralHi := (161994602472962977549/50000000000000000000)
  directionLo := (327823530185728928437/100000000000000000000)
  directionHi := (163911765092864464219/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree044.table
  base := (-1148318485809582917092122551791419594077/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-1078328420099720073288631247384717925000000000000)
      constant := (11918129797895586470983166120652951871611416721292) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree044.table
  base := (-1148454289508871641260229937257777067471/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-120100715809207062002626196904037325000000000000)
      constant := (1330639296385225700339516002742616764051745948324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327823530185728928437/100000000000000000000)
  centralHi := (163911765092864464219/50000000000000000000)
  directionLo := (331613523495912091063/100000000000000000000)
  directionHi := (41451690436989011383/12500000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree045.table
  base := (-4161100568864132559052677863904606772853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-122536556162855966670427441805717605000000000000)
      constant := (1386992372307593653619199842305895244223626572083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree045.table
  base := (-832313585256202466072142666629095680089/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-122829513229122271753950683254765105000000000000)
      constant := (1393689616804283200486985519448680298477910500395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331613523495912091063/100000000000000000000)
  centralHi := (41451690436989011383/12500000000000000000)
  directionLo := (83840171974460636179/25000000000000000000)
  directionHi := (335360687897842544717/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree046.table
  base := (-1848044867335383901545241350640857160919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-1127329590831687326779062705118198965000000000000)
      constant := (13061035212032757445797552278413454683959822391762) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree046.table
  base := (-115515368437131303328383595773325948123/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-125558310649037481505275169605492885000000000000)
      constant := (1458224554480912564377377609833029168425568417696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83840171974460636179/25000000000000000000)
  centralHi := (335360687897842544717/100000000000000000000)
  directionLo := (169533221677385749483/50000000000000000000)
  directionHi := (339066443354771498967/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree047.table
  base := (-1599176230345759349327958786856871644681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-1151830176197670953524278433984939485000000000000)
      constant := (13652438436016380094595954467196462935838272637038) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree047.table
  base := (-799674576676736468607335011336549727547/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-128287108068952691256599655956220665000000000000)
      constant := (1524243786429706090868949142645981271051062769268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169533221677385749483/50000000000000000000)
  centralHi := (339066443354771498967/100000000000000000000)
  directionLo := (342732133059033121273/100000000000000000000)
  directionHi := (171366066529516560637/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree048.table
  base := (-333497721800970365388806428096378917083/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-130703417951517175585499351427964445000000000000)
      constant := (1584126506048839989316525676283849994997725564904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree048.table
  base := (-1334139621418376655614179260240692650701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-131015905488867901007924142306948445000000000000)
      constant := (1591747042115150819414941736267622853288175079222) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342732133059033121273/100000000000000000000)
  centralHi := (171366066529516560637/50000000000000000000)
  directionLo := (346359029120268638483/100000000000000000000)
  directionHi := (86589757280067159621/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree049.table
  base := (-2105055671256304499839165200223441115783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-1200831346929638207014709891718420525000000000000)
      constant := (14875133497864893244327406437385012183839711701817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree049.table
  base := (-2105311506684956078901976896659854645163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-133744702908783110759248628657676225000000000000)
      constant := (1660734094804711895744035759390038549528996056493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346359029120268638483/100000000000000000000)
  centralHi := (86589757280067159621/25000000000000000000)
  directionLo := (87487084430744480769/25000000000000000000)
  directionHi := (349948337722977923077/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree050.table
  base := (-1509639579504499682881359634611483382259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-1225331932295621833759925620585161045000000000000)
      constant := (15506421530297182577747450307118832424103715022541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree050.table
  base := (-1509859589560732053434589258315746598959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-136473500328698320510573115008404005000000000000)
      constant := (1731204754372270136960998255641243001424821560649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87487084430744480769/25000000000000000000)
  centralHi := (349948337722977923077/100000000000000000000)
  directionLo := (353501203812682549987/100000000000000000000)
  directionHi := (88375300953170637497/25000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree051.table
  base := (-881788414067742424718097496540775366797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1040502)
      previous := (520251)
      next := (520251)
      square := (9282718021300961077912905522760000000000000)
      linear := (-480519999100963268168066647232565000000000000)
      constant := (6209535253629337110546358785485655050483303803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree051.table
  base := (-881977599008665096677245021614776766771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1040502)
      previous := (520251)
      next := (520251)
      square := (9282718021300961077912905522760000000000000)
      linear := (-481668850341223288103451907817065000000000000)
      constant := (6239304018352832312709787635290593912202169029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353501203812682549987/100000000000000000000)
  centralHi := (88375300953170637497/25000000000000000000)
  directionLo := (3570187153623126833/1000000000000000000)
  directionHi := (357018715362312683301/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree052.table
  base := (-110774144558521609396581671148934473911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-1274333103027589087250357078318642085000000000000)
      constant := (16808871267504940283286837378854256890483359490578) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree052.table
  base := (-55427738403498692095437728916538130479/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-141931095168528740013222087709859565000000000000)
      constant := (1876596281701775559671957728115041633077817181476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3570187153623126833/1000000000000000000)
  centralHi := (357018715362312683301/100000000000000000000)
  directionLo := (72100381452776338811/20000000000000000000)
  directionHi := (45062738407985211757/12500000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree053.table
  base := (117760513196151833832362228472068892507/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-1298833688393572713995572807185382605000000000000)
      constant := (17480030720793571894471622703245588664432714488428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree053.table
  base := (94180440649427637248541184209886900557/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-144659892588443949764546574060587345000000000000)
      constant := (1951516903115623577464082552887526575063880927865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72100381452776338811/20000000000000000000)
  centralHi := (45062738407985211757/12500000000000000000)
  directionLo := (363951764884904317569/100000000000000000000)
  directionHi := (36395176488490431757/10000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree054.table
  base := (597975023622233164052682990885518868971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-147037141528839593415643170672458125000000000000)
      constant := (2018275410059027591624703701893595031873811692838) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree054.table
  base := (1195829823260034305159493454085573402123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-147388690008359159515871060411315125000000000000)
      constant := (2027920631064228557727166988418637381505491392947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363951764884904317569/100000000000000000000)
  centralHi := (36395176488490431757/10000000000000000000)
  directionLo := (183684613662098128687/50000000000000000000)
  directionHi := (2938953818593570059/800000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree055.table
  base := (390629662147673343461543796153135939191/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-1347834859125539967486004264918863645000000000000)
      constant := (18862214450156372170916805111382909144502514519955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree055.table
  base := (1953044967343724247942968686659854147037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-150117487428274369267195546762042905000000000000)
      constant := (2105807386128782224639364941271632794002484162293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183684613662098128687/50000000000000000000)
  centralHi := (2938953818593570059/800000000000000000)
  directionLo := (370755190397541569733/100000000000000000000)
  directionHi := (185377595198770784867/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree056.table
  base := (1371306903326314767813795410160629331947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-1372335444491523594231219993785604165000000000000)
      constant := (19573237388443056975437545083578163092198625387094) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree056.table
  base := (68563124539867539228759177033544400363/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-152846284848189579018520033112770685000000000000)
      constant := (2185177101523560843787437497184123865108870252280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370755190397541569733/100000000000000000000)
  centralHi := (185377595198770784867/50000000000000000000)
  directionLo := (18705525469006318131/5000000000000000000)
  directionHi := (374110509380126362621/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree057.table
  base := (712865429492945414416641206705485078993/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-155204003317500802330715080294704965000000000000)
      constant := (2255282998998447291934676474504211416505216971885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree057.table
  base := (3564250808009618726312140437678969810529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-155575082268104788769844519463498465000000000000)
      constant := (2266029721063874384318253148271387170179752629081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18705525469006318131/5000000000000000000)
  centralHi := (374110509380126362621/100000000000000000000)
  directionLo := (47179500191191011087/12500000000000000000)
  directionHi := (377436001529528088697/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree058.table
  base := (883654402094805305606835526841305380023/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-1421336615223490847721651451519085205000000000000)
      constant := (21035142824698310454220036213794886696141898172115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree058.table
  base := (2209103203791384776948880923711972942261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-158303879688019998521169005814226245000000000000)
      constant := (2348365197465306552947979168991014275698754578458) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47179500191191011087/12500000000000000000)
  centralHi := (377436001529528088697/100000000000000000000)
  directionLo := (380732448410347925083/100000000000000000000)
  directionHi := (95183112102586981271/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree059.table
  base := (1326108662077755220038136505993523130357/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-1445837200589474474466867180385825725000000000000)
      constant := (21786024524823692052543325803589139853526637359828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree059.table
  base := (212175131086673216246317962636932422083/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-161032677107935208272493492164954025000000000000)
      constant := (2432183490919377259457142203599647202932156234675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380732448410347925083/100000000000000000000)
  centralHi := (95183112102586981271/25000000000000000000)
  directionLo := (384000598039219932179/100000000000000000000)
  directionHi := (19200029901960996609/5000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree060.table
  base := (6222803478612650114941205652296040620397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-163370865106162011245786989916951805000000000000)
      constant := (2505576864894404026810309002696927332096545571333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree060.table
  base := (3111377522311585003221627310493756579953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-163761474527850418023817978515681805000000000000)
      constant := (2517484567900009698503996059148446131684074119634) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (384000598039219932179/100000000000000000000)
  centralHi := (19200029901960996609/5000000000000000000)
  directionLo := (387241166866874929081/100000000000000000000)
  directionHi := (193620583433437464541/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree061.table
  base := (1793342184967092642067034188563891953859/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-1494838371321441727957298638119306765000000000000)
      constant := (23327644343375926306026176157693900776488968116236) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree061.table
  base := (1793331782346615797386126111142514992003/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-166490271947765627775142464866409585000000000000)
      constant := (2604268400162844621187564386868317942271036529068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387241166866874929081/100000000000000000000)
  centralHi := (193620583433437464541/50000000000000000000)
  directionLo := (390454841612137251693/100000000000000000000)
  directionHi := (195227420806068625847/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree062.table
  base := (326244888104459942971858574930416973009/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-1519338956687425354702514366986047285000000000000)
      constant := (24118381984451760392907910902168658414796754205225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree062.table
  base := (1631217291544399284431290517033886585173/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-169219069367680837526466951217137365000000000000)
      constant := (2692534963905793529622158857527346475844980421985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390454841612137251693/100000000000000000000)
  centralHi := (195227420806068625847/50000000000000000000)
  directionLo := (393642280961153234819/100000000000000000000)
  directionHi := (19682114048057661741/5000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree063.table
  base := (9171056926931015653754720774854426105893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-171537726894823220160858899539198645000000000000)
      constant := (2769156058126873387880016975480041347704095988477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree063.table
  base := (2292756555935155881560360409077243297979/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-171947866787596047277791437567865145000000000000)
      constant := (2782284239064489496740914611739729365718382448524) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393642280961153234819/100000000000000000000)
  centralHi := (19682114048057661741/5000000000000000000)
  directionLo := (79360823428752254107/20000000000000000000)
  directionHi := (49600514642970158817/12500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree064.table
  base := (10218167058774573898232773154453283963311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-1568340127419392608192945824719528325000000000000)
      constant := (25739711804121820609426289509061435087195022064111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree064.table
  base := (1021814068871965555885802987670117428547/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-174676664207511257029115923918592925000000000000)
      constant := (2873516208720667289220724357522797848198076966830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79360823428752254107/20000000000000000000)
  centralHi := (49600514642970158817/12500000000000000000)
  directionLo := (12498154918677782967/3125000000000000000)
  directionHi := (79988191479537810989/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree065.table
  base := (353045239336144379268018140122861813197/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-1592840712785376234938161553586268845000000000000)
      constant := (26570303696335906803861171980446760119781765593504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree065.table
  base := (11297425012510553741913020268085278161211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-177405461627426466780440410269320705000000000000)
      constant := (2966230858605138241523818099713222803359006375779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498154918677782967/3125000000000000000)
  centralHi := (79988191479537810989/20000000000000000000)
  directionLo := (403053385330182341789/100000000000000000000)
  directionHi := (40305338533018234179/10000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree066.table
  base := (2481778911643959746189188672329493208543/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-179704588683484429075930809161445485000000000000)
      constant := (3046020009908662557766639790328029461518401621635) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree066.table
  base := (6204437555919681747267346769574630719263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-180134259047341676531764896620048485000000000000)
      constant := (3060428176680047324163828312316161239505042676814) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (403053385330182341789/100000000000000000000)
  centralHi := (40305338533018234179/10000000000000000000)
  directionLo := (40614196218571254733/10000000000000000000)
  directionHi := (406141962185712547331/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree067.table
  base := (3388126059539724680510414424554938026279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-1641841883517343488428593011319749885000000000000)
      constant := (28271340889278924277195943025016012704374373909916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree067.table
  base := (542099501646360005411688560719784182641/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-182863056467256886283089382970776265000000000000)
      constant := (3156108152787615077809360244426481522030448076225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40614196218571254733/10000000000000000000)
  centralHi := (406141962185712547331/100000000000000000000)
  directionLo := (409207228027561941393/100000000000000000000)
  directionHi := (204603614013780970697/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree068.table
  base := (7364136863667061637230982061708106022579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 918090000000000000000000000000000000000000000
      center := (9364518)
      previous := (4682259)
      next := (4682259)
      square := (83544462191708649701216149704840000000000000)
      linear := (-5765890895790059222054701523136645000000000000)
      constant := (100836629819389191429188865329473169011653910822) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree068.table
  base := (14728259392423152187677988901675031708487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1040502)
      previous := (520251)
      next := (520251)
      square := (9282718021300961077912905522760000000000000)
      linear := (-642186345630353273475480516683405000000000000)
      constant := (11256992312645889827356221810675911998458275887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409207228027561941393/100000000000000000000)
  centralHi := (204603614013780970697/50000000000000000000)
  directionLo := (412249702840331214021/100000000000000000000)
  directionHi := (206124851420165607011/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree069.table
  base := (7968100258249388012167539185757507845851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-187871450472145637991002718783692325000000000000)
      constant := (3336168378686030655876515737457792903595534057478) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree069.table
  base := (7968094105371981040984265307069544671717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-188320651307087305785738355672231825000000000000)
      constant := (3351916046143960681918723342128138422513394997626) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (412249702840331214021/100000000000000000000)
  centralHi := (206124851420165607011/50000000000000000000)
  directionLo := (41526988755974313287/10000000000000000000)
  directionHi := (415269887559743132871/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree070.table
  base := (17176282486165748627542971285670484612181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-1715343639615294368664240197919971445000000000000)
      constant := (30922529004155393348995198507592399394788560648981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree070.table
  base := (4294067980847455103668105952819961617293/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-191049448727002515537062842022959605000000000000)
      constant := (3452043950044913385612956357784488228797454812308) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41526988755974313287/10000000000000000000)
  centralHi := (415269887559743132871/100000000000000000000)
  directionLo := (104567066258879407197/25000000000000000000)
  directionHi := (418268265035517628789/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree071.table
  base := (18448517845754144180067231486040510361673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-1739844224981277995409455926786711965000000000000)
      constant := (31832826758237702049399416082157049556864707736073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree071.table
  base := (1844850877999214769681478005825958215781/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-193778246146917725288387328373687385000000000000)
      constant := (3553654484897277916051574660383415684554035925090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104567066258879407197/25000000000000000000)
  centralHi := (418268265035517628789/100000000000000000000)
  directionLo := (210622650466279583789/50000000000000000000)
  directionHi := (421245300932559167579/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree072.table
  base := (19752905082305802148363622786351400101243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-196038312260806846906074628405939165000000000000)
      constant := (3639600958919798245482079035265187532773073374627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree072.table
  base := (4938224325543665483521861528038285023317/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-196507043566832935039711814724415165000000000000)
      constant := (3656747646342669418426260320739138808624422364852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210622650466279583789/50000000000000000000)
  centralHi := (421245300932559167579/100000000000000000000)
  directionLo := (26512590285951191249/6250000000000000000)
  directionHi := (84840288915043811997/20000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree073.table
  base := (21089442917252857204885004319947166599131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-1788845395713245248899887384520193005000000000000)
      constant := (33693274586352853093082476106547363264388589595931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree073.table
  base := (5272359060276678588739609342545464256739/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-199235840986748144791036301075142945000000000000)
      constant := (3761323430699423994230796381896036454450741687084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26512590285951191249/6250000000000000000)
  centralHi := (84840288915043811997/20000000000000000000)
  directionLo := (53392141217370850923/12500000000000000000)
  directionHi := (85427425947793361477/20000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree074.table
  base := (2245813026996127033109470303568675268797/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-1813345981079228875645103113386933525000000000000)
      constant := (34643424597789460789525641592371087472406123103970) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree074.table
  base := (2807265567715406395665912269049911668773/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-201964638406663354542360787425870725000000000000)
      constant := (3867381834857115964090387025569071002833450598376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53392141217370850923/12500000000000000000)
  centralHi := (85427425947793361477/20000000000000000000)
  directionLo := (430052775393419914581/100000000000000000000)
  directionHi := (215026387696709957291/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree075.table
  base := (11929483113489703348625572147613108032119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-204205174049468055821146538028186005000000000000)
      constant := (3956317626705730760956222854839114847590603341182) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree075.table
  base := (23858961312555655467143354667663284082939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-204693435826578564293685273776598505000000000000)
      constant := (3974922856187616504682674938911987939758787553571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (430052775393419914581/100000000000000000000)
  centralHi := (215026387696709957291/50000000000000000000)
  directionLo := (54118598300041974763/12500000000000000000)
  directionHi := (86589757280067159621/20000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree076.table
  base := (316149375201146984759466977908114435391/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-1862347151811196129135534571120414565000000000000)
      constant := (36583576693550160880112500005434845157956540815280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree076.table
  base := (5058389160057328902468471147688556990323/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-207422233246493774045009760127326285000000000000)
      constant := (4083946492470079221228202131735070946445221713735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54118598300041974763/12500000000000000000)
  centralHi := (86589757280067159621/20000000000000000000)
  directionLo := (43582555416985808759/10000000000000000000)
  directionHi := (435825554169858087591/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree077.table
  base := (3344635123052659876731453320188696804613/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-1886847737177179755880750299987155085000000000000)
      constant := (37573578740062556103462168841307189490629060888104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree077.table
  base := (535141547365679020737931042023378130129/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-210151030666408983796334246478054065000000000000)
      constant := (4194452741827655529560828300739634479163693674050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43582555416985808759/10000000000000000000)
  centralHi := (435825554169858087591/100000000000000000000)
  directionLo := (219341728639014457843/50000000000000000000)
  directionHi := (438683457278028915687/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree078.table
  base := (7063589644986008459600475312322459510893/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-212372035838129264736218447650432845000000000000)
      constant := (4286318307249113482479985848777759404348036133908) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree078.table
  base := (28254355478486203399910912770170275236651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-212879828086324193547658732828781845000000000000)
      constant := (4306441602674092618621118854922161604052143209939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219341728639014457843/50000000000000000000)
  centralHi := (438683457278028915687/100000000000000000000)
  directionLo := (27595178878020334213/6250000000000000000)
  directionHi := (441522862048325347409/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree079.table
  base := (14891891167940401141669584617745385289693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-1935848907909147009371181757720636125000000000000)
      constant := (39593434756703596415725210517712155030619503440186) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree079.table
  base := (29783779676113984977041603493725879535187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-215608625506239403298983219179509625000000000000)
      constant := (4419913073668660292832428604307330375723009907643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27595178878020334213/6250000000000000000)
  centralHi := (441522862048325347409/100000000000000000000)
  directionLo := (444344123099748951713/100000000000000000000)
  directionHi := (222172061549874475857/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree080.table
  base := (31345351857514969937632936117190590984939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-1960349493275130636116397486587376645000000000000)
      constant := (40623288703974343942116578164519813229675780484139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree080.table
  base := (15672674788381310884704752865454621817687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-218337422926154613050307705530237405000000000000)
      constant := (4534867153678099361230076007194939401159766100286) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444344123099748951713/100000000000000000000)
  centralHi := (222172061549874475857/50000000000000000000)
  directionLo := (447147583863790059621/100000000000000000000)
  directionHi := (223573791931895029811/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree081.table
  base := (514672918922769435786311129729182184969/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-220538897626790473651290357272679685000000000000)
      constant := (4629602955355322115195198003287143081124196751424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree081.table
  base := (16469532427751711589074340304519407564167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-221066220346069822801632191880965185000000000000)
      constant := (4651303841744491125275140976719763795202875053726) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447147583863790059621/100000000000000000000)
  centralHi := (223573791931895029811/50000000000000000000)
  directionLo := (112483394268100046703/25000000000000000000)
  directionHi := (449933577072400186813/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree082.table
  base := (17282463457118765989878387662330217211739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-2009350664007097889606828944320857685000000000000)
      constant := (42722848431884845516068961611290899004131691501878) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree082.table
  base := (34564925237679058298570273979749607255601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-223795017765985032552956678231692965000000000000)
      constant := (4769223137058121328958150253544404372404557496489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112483394268100046703/25000000000000000000)
  centralHi := (449933577072400186813/100000000000000000000)
  directionLo := (45270242521893539511/10000000000000000000)
  directionHi := (452702425218935395111/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree083.table
  base := (9055732982088656340602161164917236874279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-2033851249373081516352044673187598205000000000000)
      constant := (43792554198701771707348484181762846597320426901916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree083.table
  base := (36222930491128304596915413843035054866357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-226523815185900242304281164582420745000000000000)
      constant := (4888625038934558025900777178473233778115903541773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45270242521893539511/10000000000000000000)
  centralHi := (452702425218935395111/100000000000000000000)
  directionLo := (22772722049693911601/5000000000000000000)
  directionHi := (455454440993878232021/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree084.table
  base := (37913081651556630977904857610082315957683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-228705759415451682566362266894926525000000000000)
      constant := (4986171543699220166727905314466921974769369717787) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree084.table
  base := (18956540209808537475873886167136597765609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-229252612605815452055605650933148525000000000000)
      constant := (5009509546795285662435273649128166515740432942402) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22772722049693911601/5000000000000000000)
  centralHi := (455454440993878232021/100000000000000000000)
  directionLo := (458189927697004730577/100000000000000000000)
  directionHi := (229094963848502365289/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree085.table
  base := (39635375913160703286973069365625132946787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 918090000000000000000000000000000000000000000
      center := (9364518)
      previous := (4682259)
      next := (4682259)
      square := (83544462191708649701216149704840000000000000)
      linear := (-7207101799671449030596803221180205000000000000)
      constant := (159072032910483671006469556217836790330711567683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree085.table
  base := (1238605464290240059061102253764400990447/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1040502)
      previous := (520251)
      next := (520251)
      square := (9282718021300961077912905522760000000000000)
      linear := (-802703840919483258847509125549745000000000000)
      constant := (17757358685644778597082076659365489694113595104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (458189927697004730577/100000000000000000000)
  centralHi := (229094963848502365289/50000000000000000000)
  directionLo := (230454589813767181393/50000000000000000000)
  directionHi := (460909179627534362787/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree086.table
  base := (10347453642212649250901211580803556888353/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-2107353005471032396587691859787819765000000000000)
      constant := (47081375048383055751063296078908131735043397467012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree086.table
  base := (8277962732793559296458793028992120466377/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-234710207445645871558254623634604085000000000000)
      constant := (5255726378589483581244430833176269814668004517765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230454589813767181393/50000000000000000000)
  centralHi := (460909179627534362787/100000000000000000000)
  directionLo := (115903120613420891361/25000000000000000000)
  directionHi := (92722496490736713089/20000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree087.table
  base := (43176397496615804309949976010846909731671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-236872621204112891481434176517173365000000000000)
      constant := (5356024055757280607476885210081647812763932226719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree087.table
  base := (21588198360602696553036570110730877247751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-237439004865561081309579109985331865000000000000)
      constant := (5381058701760506248732433048936556713598889995678) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115903120613420891361/25000000000000000000)
  centralHi := (92722496490736713089/20000000000000000000)
  directionLo := (93260022712587276401/20000000000000000000)
  directionHi := (233150056781468191003/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree088.table
  base := (44995124593317305443227326100364614706369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-2156354176202999650078123317521300805000000000000)
      constant := (49340341868690622982854775191817230249445762109569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree088.table
  base := (8999024785783377049348841657258218626933/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-240167802285476291060903596336059645000000000000)
      constant := (5507873629369353696536637766453351972468281405185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93260022712587276401/20000000000000000000)
  centralHi := (233150056781468191003/50000000000000000000)
  directionLo := (468972342394247894473/100000000000000000000)
  directionHi := (234486171197123947237/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree089.table
  base := (11711498942945720764551629055570998188699/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-2180854761568983276823339046388041325000000000000)
      constant := (50489751146695425202201975000657523347748444063596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree089.table
  base := (23422997601276638168936552126475815160681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-242896599705391500812228082686787425000000000000)
      constant := (5636171161166767957918502949219869772632473777218) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468972342394247894473/100000000000000000000)
  centralHi := (234486171197123947237/50000000000000000000)
  directionLo := (117907357688326642101/25000000000000000000)
  directionHi := (94325886150661313681/20000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree090.table
  base := (3045563184896878692571852020729792533337/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-245039482992774100396506086139420205000000000000)
      constant := (5739160481541717805937357213082946698437007087888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree090.table
  base := (12182252617675999315456212483603222831003/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-245625397125306710563552569037515205000000000000)
      constant := (5765951296942224319578589212027685628870515213068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117907357688326642101/25000000000000000000)
  centralHi := (94325886150661313681/20000000000000000000)
  directionLo := (94854326622379921899/20000000000000000000)
  directionHi := (59283954138987451187/12500000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree091.table
  base := (25322085045393726693046839147524090933453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-2229855932300950530313770504121522365000000000000)
      constant := (52828421428579555311719963833310442162386425383706) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree091.table
  base := (25322084836535309118991422326649755306481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-248354194545221920314877055388242985000000000000)
      constant := (5897214036517957643963388341202436677193456529618) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94854326622379921899/20000000000000000000)
  centralHi := (59283954138987451187/12500000000000000000)
  directionLo := (476899196892350223031/100000000000000000000)
  directionHi := (59612399611543777879/12500000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree092.table
  base := (52591473116536110725560959492780122965279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-2254356517666934157058986232988262885000000000000)
      constant := (54017682429413174076703990324068183969393277616479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree092.table
  base := (26295736379376588291229044340071080983853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-251082991965137130066201541738970765000000000000)
      constant := (6029959379743910310984116699420671421133212413834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476899196892350223031/100000000000000000000)
  centralHi := (59612399611543777879/12500000000000000000)
  directionLo := (479512362737926642479/100000000000000000000)
  directionHi := (5993904534224083031/1250000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree093.table
  base := (54570919991221410365841310691241233094487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-253206344781435309311577995761667045000000000000)
      constant := (6135580815022103729667809842688743188132293085343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree093.table
  base := (3410682480300047709068083723403154809711/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-253811789385052339817526028089698545000000000000)
      constant := (6164187326493459218424802379617247050906897476464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479512362737926642479/100000000000000000000)
  centralHi := (5993904534224083031/1250000000000000000)
  directionLo := (120527841192514845269/25000000000000000000)
  directionHi := (482111364770059381077/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree094.table
  base := (56582510677393826152388169366214632771973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-2303357688398901410549417690721743925000000000000)
      constant := (56436056144943192957635979425012852189626837986373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree094.table
  base := (1414562760374638043398502870851159300399/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-256540586804967549568850514440426325000000000000)
      constant := (6299897876659801420189458327028799882330159500440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120527841192514845269/25000000000000000000)
  centralHi := (482111364770059381077/100000000000000000000)
  directionLo := (484696430833144848621/100000000000000000000)
  directionHi := (242348215416572424311/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree095.table
  base := (58626245143463265590750444562435712541227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-2327858273764885037294633419588484445000000000000)
      constant := (57665168857807778610854198445961738673649580286827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree095.table
  base := (58626244918765547666084086057984918013929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-259269384224882759320175000791154105000000000000)
      constant := (6437091030152896664794465811086116580212765931681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484696430833144848621/100000000000000000000)
  centralHi := (242348215416572424311/50000000000000000000)
  directionLo := (9745355654553196097/2000000000000000000)
  directionHi := (487267782727659804851/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree096.table
  base := (60702123362797172042204193068610761327623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-261373206570096518226649905383913885000000000000)
      constant := (6545285052565117133472050485320532350751590762447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree096.table
  base := (1517553079260188298847499038417387695203/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-261998181644797969071499487141881885000000000000)
      constant := (6575766786896880866507888099534420842918532682680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9745355654553196097/2000000000000000000)
  centralHi := (487267782727659804851/100000000000000000000)
  directionLo := (244912818216130838249/50000000000000000000)
  directionHi := (489825636432261676499/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree097.table
  base := (62810145312957181766596521160004363030399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-2376859444496852290785064877321965485000000000000)
      constant := (60163245990182667088935654752009456065917333617599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree097.table
  base := (62810145148244499874755263540414194200173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-264726979064713178822823973492609665000000000000)
      constant := (6715925146827877855480758155735850605115393819397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244912818216130838249/50000000000000000000)
  centralHi := (489825636432261676499/100000000000000000000)
  directionLo := (98474040463100834819/20000000000000000000)
  directionHi := (30773137644719010881/6250000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree098.table
  base := (64950310975053019895142433206904020377443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-2401360029862835917530280606188706005000000000000)
      constant := (61432210408596405369987026197506702023774640007843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree098.table
  base := (12990062166809563461237190133180853063643/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-267455776484628388574148459843337445000000000000)
      constant := (6857566109892147995971615086333979152137711141135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98474040463100834819/20000000000000000000)
  centralHi := (30773137644719010881/6250000000000000000)
  directionLo := (494901685337755569981/100000000000000000000)
  directionHi := (247450842668877784991/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree099.table
  base := (67122620333195608179747924902738186372717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-269540068358757727141721815006160725000000000000)
      constant := (6968273191989520810352495762090791464625356887813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree099.table
  base := (16780655053123963418273842298961506169659/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-270184573904543598325472946194065225000000000000)
      constant := (7000689676044521757419952772567967177298815326604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494901685337755569981/100000000000000000000)
  centralHi := (247450842668877784991/50000000000000000000)
  directionLo := (99484057048773627319/20000000000000000000)
  directionHi := (124355071310967034149/25000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree100.table
  base := (69327073374034136665941000485238911375041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-2450361200594803171020712063922187045000000000000)
      constant := (64009990947756278474781137212307620722970599219841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree100.table
  base := (17331768317681103207403963302465480481651/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-272913371324458808076797432544793005000000000000)
      constant := (7145295845247074344674296353082274748550680059756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99484057048773627319/20000000000000000000)
  centralHi := (124355071310967034149/25000000000000000000)
  directionLo := (12498154918677782967/2500000000000000000)
  directionHi := (499926196747111318681/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree101.table
  base := (71563670086364200614058257797859611969187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (265302)
      previous := (132651)
      next := (132651)
      square := (2366861050230742060940247746760000000000000)
      linear := (-242609723160551592762075070364565000000000000)
      constant := (6403176852058709408247437153374725350731855387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree101.table
  base := (71563669997946341955631113851438778233379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (29478)
      previous := (14739)
      next := (14739)
      square := (262984561136749117882249749640000000000000)
      linear := (-27021092907006569731214774913785000000000000)
      constant := (714771553521027768960331537886304556909446531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498154918677782967/2500000000000000000)
  centralHi := (499926196747111318681/100000000000000000000)
  directionLo := (502419609704847975679/100000000000000000000)
  directionHi := (392515320081912481/78125000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree102.table
  base := (36916205230398044974125382820859542662477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1040502)
      previous := (520251)
      next := (520251)
      square := (9282718021300961077912905522760000000000000)
      linear := (-960923633728093204348767213247085000000000000)
      constant := (25621263778523798762220367100752931389399855754) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree102.table
  base := (36916205192564835633771374860928538084279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1040502)
      previous := (520251)
      next := (520251)
      square := (9282718021300961077912905522760000000000000)
      linear := (-963221336208613244219537734416085000000000000)
      constant := (25740332154604444588659968649392981533995460158) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (502419609704847975679/100000000000000000000)
  centralHi := (392515320081912481/78125000000000000)
  directionLo := (504900709286402255439/100000000000000000000)
  directionHi := (6311258866080028193/1250000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree103.table
  base := (3045331779578959906904143991804550331251/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-2523862956692754051256359250522408605000000000000)
      constant := (67976291007816359632073323997451483658339171601275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree103.table
  base := (76133294424725279299281971486933820365301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-281099763584204437330770891596976345000000000000)
      constant := (7588009970862859507595681847091989170796919859789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504900709286402255439/100000000000000000000)
  centralHi := (6311258866080028193/1250000000000000000)
  directionLo := (507369676133539142849/100000000000000000000)
  directionHi := (10147393522670782857/2000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree104.table
  base := (9808290270729791708213283614470786037233/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-2548363542058737678001574979389149125000000000000)
      constant := (69324958827304727528813603500658033029915854237064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree104.table
  base := (9808290263804558308780829516080441231307/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-283828561004119647082095377947704125000000000000)
      constant := (7738546551995966104813316949022577585273300978584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507369676133539142849/100000000000000000000)
  centralHi := (10147393522670782857/2000000000000000000)
  directionLo := (25491334325697464059/5000000000000000000)
  directionHi := (509826686513949281181/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree105.table
  base := (10103936685553066403281292822631047241297/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-285873791936080144971865634250654405000000000000)
      constant := (7854101171806723778879885590516897793944384251464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree105.table
  base := (80831493437023993076744977136547207103829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-286557358424034856833419864298431905000000000000)
      constant := (7890565736064558532836819289226343312993520132781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25491334325697464059/5000000000000000000)
  centralHi := (509826686513949281181/100000000000000000000)
  directionLo := (256135956234054060431/50000000000000000000)
  directionHi := (512271912468108120863/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree106.table
  base := (41614404220346374803654106816690470726809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-2597364712790704931492006437122630165000000000000)
      constant := (72062146164563264384279502877315403481781497124018) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree106.table
  base := (83228808400141130015448630500204050518083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-289286155843950066584744350649159685000000000000)
      constant := (8044067523055822247410686654376109941587804793387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256135956234054060431/50000000000000000000)
  centralHi := (512271912468108120863/100000000000000000000)
  directionLo := (25735276097492782823/5000000000000000000)
  directionHi := (514705521949855656461/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree107.table
  base := (21414566757720933795305200032248854951831/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-2621865298156688558237222165989370685000000000000)
      constant := (73450665682113235123483994671591298671159186034524) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree107.table
  base := (85658266996194109571044271185316462767811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-292014953263865276336068836999887465000000000000)
      constant := (8199051912959162501464848699384840101654693163179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25735276097492782823/5000000000000000000)
  centralHi := (514705521949855656461/100000000000000000000)
  directionLo := (517127678961021827767/100000000000000000000)
  directionHi := (64640959870127728471/12500000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree108.table
  base := (44059934625948415501932601445141230986573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-294040653724741353886937543872901245000000000000)
      constant := (8316941010980906345984973854895243683035950017994) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree108.table
  base := (88119869222224073197787561900084700808841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-294743750683780486087393323350615245000000000000)
      constant := (8355518905765856316668040546670289180522835254849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (517127678961021827767/100000000000000000000)
  centralHi := (64640959870127728471/12500000000000000000)
  directionLo := (129884635920100739431/25000000000000000000)
  directionHi := (20781541747216118309/4000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree109.table
  base := (4530680755059336991221830488845320882799/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-2670866468888655811727653623722851725000000000000)
      constant := (76267556414640496489980361774351177027789003799980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree109.table
  base := (18122723015161442685332855233093318395563/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-297472548103695695838717809701343025000000000000)
      constant := (8513468501468758092882743514306084218427284645535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129884635920100739431/25000000000000000000)
  centralHi := (20781541747216118309/4000000000000000000)
  directionLo := (521938272587376261893/100000000000000000000)
  directionHi := (260969136293688130947/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree110.table
  base := (93139504576676166273990668263453709686071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-2695367054254639438472869352589592245000000000000)
      constant := (77695927629495136787188363826842604426812294314871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree110.table
  base := (93139504554970314753446900011959518427233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-300201345523610905590042296052070805000000000000)
      constant := (8672900700062050615186315014861388212220622907737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521938272587376261893/100000000000000000000)
  centralHi := (260969136293688130947/50000000000000000000)
  directionLo := (524327018580422385231/100000000000000000000)
  directionHi := (32770438661276399077/6250000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree111.table
  base := (19139507535336380929539730821793234238531/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-302207515513402562802009453495148085000000000000)
      constant := (8793064749260824204831165063573584028165183086295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree111.table
  base := (95697537658119327898335625012125803910061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-302930142943526115341366782402798585000000000000)
      constant := (8833815501541034484431519310909164850373407823429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (524327018580422385231/100000000000000000000)
  centralHi := (32770438661276399077/6250000000000000000)
  directionLo := (526704931090810004911/100000000000000000000)
  directionHi := (32919058193175625307/6250000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree112.table
  base := (19657542879970462339837527896123606277007/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-2744368224986606691963300810323073285000000000000)
      constant := (80592521756161476777577720144334405063750888033035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree112.table
  base := (12285964297997371906067633598353309275913/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-305658940363441325092691268753526365000000000000)
      constant := (8996212905901950068716145764940680693519336642056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526704931090810004911/100000000000000000000)
  centralHi := (32919058193175625307/6250000000000000000)
  directionLo := (264536078095840847023/50000000000000000000)
  directionHi := (529072156191681694047/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree113.table
  base := (50455017372557209805579350098542936704403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-2768868810352590318708516539189813805000000000000)
      constant := (82060744667908844747904270830541908721567041245606) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree113.table
  base := (12613754341442711600423872873142822668503/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-308387737783356534844015755104254145000000000000)
      constant := (9160092913141826979693016528987323451253714726136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264536078095840847023/50000000000000000000)
  centralHi := (529072156191681694047/100000000000000000000)
  directionLo := (106285767340553277837/20000000000000000000)
  directionHi := (265714418351383194593/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree114.table
  base := (6472781169476825725326631344023521230587/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-310374377302063771717081363117394925000000000000)
      constant := (9282472386507473365471507536590919723898559971888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree114.table
  base := (20712899740004894831967453197789439151899/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-311116535203271744595340241454981925000000000000)
      constant := (9325455523258356844798375928197810921899413855055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106285767340553277837/20000000000000000000)
  centralHi := (265714418351383194593/50000000000000000000)
  directionLo := (33360944518183179369/6250000000000000000)
  directionHi := (106755022458186173981/20000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree115.table
  base := (5312555314937690447795539590926141185773/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-2817869981084557572198947996923294845000000000000)
      constant := (85037042188119666028305341835317390683100380803460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree115.table
  base := (53125553144416201146534982861395605865773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-313845332623186954346664727805709705000000000000)
      constant := (9492300736249785795695469015767984426852441715594) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33360944518183179369/6250000000000000000)
  centralHi := (106755022458186173981/20000000000000000000)
  directionLo := (53611111956677057341/10000000000000000000)
  directionHi := (536111119566770573411/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree116.table
  base := (54484928753004754889980343713264571542217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-2842370566450541198944163725790035365000000000000)
      constant := (86545116796553360663282940078546979404159813519634) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree116.table
  base := (5448492874876392063200868034275399698973/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-316574130043102164097989214156437485000000000000)
      constant := (9660628552114823642686313779329191121462912251940) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53611111956677057341/10000000000000000000)
  centralHi := (536111119566770573411/100000000000000000000)
  directionLo := (538436992177428768211/100000000000000000000)
  directionHi := (134609248044357192053/25000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree117.table
  base := (55860376166527391106194337366325106098963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-318541239090724980632153272739641765000000000000)
      constant := (9785163922651031377463055622934082763928371463414) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree117.table
  base := (111720752325804417732667698763103201314577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-319302927463017373849313700507165265000000000000)
      constant := (9830438970852567169897328312603437542410289993353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (538436992177428768211/100000000000000000000)
  centralHi := (134609248044357192053/25000000000000000000)
  directionLo := (270376430447911270541/50000000000000000000)
  directionHi := (540752860895822541083/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree118.table
  base := (57251895389831225981786026140909628826649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-2891371737182508452434595183523516405000000000000)
      constant := (89601117710031403659740147916106989956282682827698) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree118.table
  base := (114503790773465055678974404847589725319773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-322031724882932583600638186857893045000000000000)
      constant := (10001731992462435379681649528027193083228244263797) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270376430447911270541/50000000000000000000)
  centralHi := (540752860895822541083/100000000000000000000)
  directionLo := (271529426853222078927/50000000000000000000)
  directionHi := (108611770741288831571/20000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree119.table
  base := (117318972845700440592149530630403002349573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 918090000000000000000000000000000000000000000
      center := (9364518)
      previous := (4682259)
      next := (4682259)
      square := (83544462191708649701216149704840000000000000)
      linear := (-10089523607434228647681006617267325000000000000)
      constant := (315394615969087266574393954137496166742711947557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree119.table
  base := (117318972840403440757535307925001594602407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1040502)
      previous := (520251)
      next := (520251)
      square := (9282718021300961077912905522760000000000000)
      linear := (-1123738831497743229591566343282425000000000000)
      constant := (35205908709149186324868702715079812516539153807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271529426853222078927/50000000000000000000)
  centralHi := (108611770741288831571/20000000000000000000)
  directionLo := (109071019177579418491/20000000000000000000)
  directionHi := (68169386985987136557/12500000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree120.table
  base := (7510393658194719334634238071544384180353/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-326708100879386189547225182361888605000000000000)
      constant := (10301139357662479884994142395585338492221963126672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree120.table
  base := (120166298526588386389755315817687775188789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-327489319722763003103287159559348605000000000000)
      constant := (10348765844297513633704241155793136685468541774221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109071019177579418491/20000000000000000000)
  centralHi := (68169386985987136557/12500000000000000000)
  directionLo := (273820855046158667657/50000000000000000000)
  directionHi := (109528342018463467063/20000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree121.table
  base := (123045767835919546931364990368749100193287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-2964873493280459332670242370123737965000000000000)
      constant := (94284748321720015874610735736679721536857545506887) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree121.table
  base := (123045767832050654693703048894092680742833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-330218117142678212854611645910076385000000000000)
      constant := (10524506674522722426595102542385792610828457796137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273820855046158667657/50000000000000000000)
  centralHi := (109528342018463467063/20000000000000000000)
  directionLo := (137479704105455612637/25000000000000000000)
  directionHi := (549918816421822450549/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree122.table
  base := (25191476152035602002678860243191521358251/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-2989374078646442959415458098990478485000000000000)
      constant := (95872526323341047518309311135613505410428617455255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree122.table
  base := (12595738075687185392270067631785586865661/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-332946914562593422605936132260804165000000000000)
      constant := (10701730107619981814953567544803498572471996718290) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137479704105455612637/25000000000000000000)
  centralHi := (549918816421822450549/100000000000000000000)
  directionLo := (69023316562765401667/12500000000000000000)
  directionHi := (552186532502123213337/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree123.table
  base := (1007040135187501449723434166562736247617/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-334874962668047398462297091984135445000000000000)
      constant := (10830398691536479287257818599267080116812122100864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree123.table
  base := (128901137301175092137045661455968599635579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-335675711982508632357260618611531945000000000000)
      constant := (10880436143589654732298010451526384469181054458531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69023316562765401667/12500000000000000000)
  centralHi := (552186532502123213337/100000000000000000000)
  directionLo := (554444973553425489457/100000000000000000000)
  directionHi := (277222486776712744729/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree124.table
  base := (65938518733765497153145268183134114545387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-3038375249378410212905889556723959525000000000000)
      constant := (99087934023185659228303192027154258625087917477974) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree124.table
  base := (26375407493023423196757825868975545179601/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-338404509402423842108585104962259725000000000000)
      constant := (11060624782432203281694389566712023865064923662445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554444973553425489457/100000000000000000000)
  centralHi := (277222486776712744729/50000000000000000000)
  directionLo := (556694252458743285867/100000000000000000000)
  directionHi := (139173563114685821467/25000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree125.table
  base := (26977016250188819577516082322180794851601/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-3062875834744393839651105285590700045000000000000)
      constant := (100715563721417692177235037962925702391596769322005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree125.table
  base := (67442540624440852536767042888256285795551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-341133306822339051859909591312987505000000000000)
      constant := (11242296024148169261791147895102539889419440304078) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556694252458743285867/100000000000000000000)
  centralHi := (139173563114685821467/25000000000000000000)
  directionLo := (558934479829737574527/100000000000000000000)
  directionHi := (4366675623669824801/781250000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree126.table
  base := (68962634327218054296585135259950356942551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-343041824456708607377369001606382285000000000000)
      constant := (11372941924281069900748892674934581470696816470078) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree126.table
  base := (34481317163168531919273702436235471445463/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-343862104242254261611234077663715285000000000000)
      constant := (11425449868738157821719522033643277686612734280828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558934479829737574527/100000000000000000000)
  centralHi := (4366675623669824801/781250000000000000)
  directionLo := (561165764070189543931/100000000000000000000)
  directionHi := (140291441017547385983/25000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree127.table
  base := (17624699959777716405977636380760461914429/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-3111877005476361093141536743324181085000000000000)
      constant := (104010674814527166737207303262198550834648989485032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree127.table
  base := (14099759967671649329723762584975250448271/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-346590901662169471362558564014443065000000000000)
      constant := (11610086316202823760061412853456708612437928041190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (561165764070189543931/100000000000000000000)
  centralHi := (140291441017547385983/25000000000000000000)
  directionLo := (563388211437211338329/100000000000000000000)
  directionHi := (56338821143721133833/10000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree128.table
  base := (144102074322529693076729931929119522881529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (2706345702)
      previous := (1353172851)
      next := (1353172851)
      square := (24144349573403799763651467264698760000000000000)
      linear := (-3136377590842344719886752472190921605000000000000)
      constant := (105678156209416373842586281271612540005830555532729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree128.table
  base := (144102074321243862929952783176843260216717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-349319699082084681113883050365170845000000000000)
      constant := (11796205366542860057553428251980231070169041003813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell072.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (563388211437211338329/100000000000000000000)
  centralHi := (56338821143721133833/10000000000000000000)
  directionLo := (565601926100292079979/100000000000000000000)
  directionHi := (28280096305014603999/5000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree129.table
  base := (4601209143362479355912989876392994222257/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-351208686245369816292440911228629125000000000000)
      constant := (11928769055911511213815489940836993792698381339936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree129.table
  base := (147238692586500999216956581666538796833897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (300705078)
      previous := (150352539)
      next := (150352539)
      square := (2682705508155977751516829696077640000000000000)
      linear := (-352048496501999890865207536715898625000000000000)
      constant := (11983807019758988296247222994188616798769246572833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell072.Kernel129
