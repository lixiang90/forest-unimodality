import ForestUnimodality.FiniteKernelDegreeCertificate
import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell291.Parameters
import ForestUnimodality.BinomialMassData.Q3_5.Batch000_049
import ForestUnimodality.BinomialMassData.Q3_5.Batch050_099
import ForestUnimodality.BinomialMassData.Q3_5.Batch100_149
import ForestUnimodality.BinomialMassData.Q123_203.Batch000_049
import ForestUnimodality.BinomialMassData.Q123_203.Batch050_099
import ForestUnimodality.BinomialMassData.Q123_203.Batch100_149

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree000.table
  base := (1993780326708938859358255529/100000000000000000000000000)
  polynomial :=
    { denominator := 1000000000000000000000000000000000000000
      center := (3)
      previous := (0)
      next := (2)
      square := (13864452005630176212314097000000000000)
      linear := (-48342280904976747679668847000000000000)
      constant := (19937803267089388593582555290000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree000.table
  base := (1993780326708938859358255529/100000000000000000000000000)
  polynomial :=
    { denominator := 40600000000000000000000000000000000000000
      center := (123)
      previous := (0)
      next := (80)
      square := (562896751428585154219952338200000000000)
      linear := (-1962696604742055955794555188200000000000)
      constant := (809474812643829176899451744774000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree000.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel000

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree001.table
  base := (163562075237736589797722581889833495110291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-649796233117329591344457634000000000000)
      constant := (163902040950386718918164925721033495110291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree001.table
  base := (16321135499988312074675389868392216506103/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 41209000000000000000000000000000000000000000
      center := (124845)
      previous := (0)
      next := (81200)
      square := (571340202700013931533251623273000000000000)
      linear := (-2684500058070346534822014892009000000000000)
      constant := (673994486525327895634027892500830849999998527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree001.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel001

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (48865405980836431213/100000000000000000000)
  directionHi := (24432702990418215607/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree002.table
  base := (33536815285777531421113204644940728966973/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-408084828592445852946113399000000000000)
      constant := (67463508311425460597033083870281457933946) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree002.table
  base := (133572701919954708602727964949428571428571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1248450)
      previous := (0)
      next := (812000)
      square := (5713402027000139315332516232730000000000000)
      linear := (-33768630623275062745125562679950000000000000)
      constant := (5536928853433468032502733735356381999999982339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree002.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel002

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48865405980836431213/100000000000000000000)
  centralHi := (24432702990418215607/50000000000000000000)
  directionLo := (34553059934483117077/50000000000000000000)
  directionHi := (13821223973793246831/20000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree003.table
  base := (55000473501996444657882410152923413194111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-491271540626226910219997981000000000000)
      constant := (55660158152632444241638918147323413194111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree003.table
  base := (27323750768958262583844677079796122100293/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-20346130332923330071015488219905000000000000)
      constant := (2279513755302440603943739865981866791261948474) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree003.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel003

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34553059934483117077/50000000000000000000)
  centralHi := (13821223973793246831/20000000000000000000)
  directionLo := (84637365891288787119/100000000000000000000)
  directionHi := (1057967073641109839/1250000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree004.table
  base := (45087002330171190477792217529617856016503/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-574458252660007967493882563000000000000)
      constant := (46066405918793060524862889687217856016503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree004.table
  base := (17880601328682641773430072343743074682809/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 82418000000000000000000000000000000000000000
      center := (249690)
      previous := (0)
      next := (162400)
      square := (1142680405400027863066503246546000000000000)
      linear := (-9523178141683651507787278039934000000000000)
      constant := (753210336869595626093104261891668364603876081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree004.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel004

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84637365891288787119/100000000000000000000)
  centralHi := (1057967073641109839/1250000000000000000)
  directionLo := (48865405980836431213/50000000000000000000)
  directionHi := (97730811961672862427/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree005.table
  base := (18470056299157294595911811702446687694861/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-657644964693789024767767145000000000000)
      constant := (38289147152142598336572790474893375389722) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree005.table
  base := (36545402929332473228958879056824261959649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-27269760375494927467920901979765000000000000)
      constant := (1562395381411918366602020229760371011095175641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree005.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel005

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48865405980836431213/50000000000000000000)
  centralHi := (97730811961672862427/100000000000000000000)
  directionLo := (109266369521275045931/100000000000000000000)
  directionHi := (27316592380318761483/25000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree006.table
  base := (60485105958701489454731381617373137142043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-1481663353455140164083303454000000000000)
      constant := (64022261051210323208315367080573137142043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree006.table
  base := (59709156091058150181668814604258961949777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1248450)
      previous := (0)
      next := (812000)
      square := (5713402027000139315332516232730000000000000)
      linear := (-61463150793561452332747217719390000000000000)
      constant := (2608490024052941592535005257936167562988360393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree006.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel006

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109266369521275045931/100000000000000000000)
  centralHi := (27316592380318761483/25000000000000000000)
  directionLo := (119695310726994602561/100000000000000000000)
  directionHi := (59847655363497301281/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree007.table
  base := (4946762542438805897698281017759308730267/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1000000000000000000000000000000000000000
      center := (3)
      previous := (0)
      next := (2)
      square := (13864452005630176212314097000000000000)
      linear := (-164803677752270227863107261800000000000)
      constant := (5394369055619024546338110846239308730267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree007.table
  base := (48726101309540450149881926106214607858657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (178350)
      previous := (0)
      next := (116000)
      square := (816200289571448473618930890390000000000000)
      linear := (-9769540119447578532807518782750000000000000)
      constant := (313604013135950799674618411540625396463913759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree007.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel007

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119695310726994602561/100000000000000000000)
  centralHi := (59847655363497301281/50000000000000000000)
  directionLo := (129285711939501474187/100000000000000000000)
  directionHi := (32321427984875368547/25000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree008.table
  base := (20200179185121838459632728007242318007283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-907205100795132196589420891000000000000)
      constant := (22957578797889876703603364309642318007283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree008.table
  base := (39706194154672432112019139490063698899473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1248450)
      previous := (0)
      next := (812000)
      square := (5713402027000139315332516232730000000000000)
      linear := (-75310410878704647126558045239110000000000000)
      constant := (1867060616284839926915592817553794967948382857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree008.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel008

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129285711939501474187/100000000000000000000)
  centralHi := (32321427984875368547/25000000000000000000)
  directionLo := (138212239737932468309/100000000000000000000)
  directionHi := (13821223973793246831/10000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree009.table
  base := (32932750953289399102205726694791542136073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-1980783625657826507726610946000000000000)
      constant := (39586108326999902860418635117991542136073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree009.table
  base := (6458615033968324002087410943813938782129/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 82418000000000000000000000000000000000000000
      center := (249690)
      previous := (0)
      next := (162400)
      square := (1142680405400027863066503246546000000000000)
      linear := (-16446808184255248904692691799794000000000000)
      constant := (321860476040990210851074039226108603272753961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree009.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel009

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138212239737932468309/100000000000000000000)
  centralHi := (13821223973793246831/10000000000000000000)
  directionLo := (3664905448562732341/2500000000000000000)
  directionHi := (146596217942509293641/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree010.table
  base := (26777321655150425475110019368803792348769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-2147157049725388622274380110000000000000)
      constant := (34669061231475893772323225108803792348769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree010.table
  base := (13097567172269403058929328036650966694339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-44578835481923920960184436379415000000000000)
      constant := (704968213394457519254151237855999686507015851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree010.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel010

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3664905448562732341/2500000000000000000)
  centralHi := (146596217942509293641/100000000000000000000)
  directionLo := (154525981688257358957/100000000000000000000)
  directionHi := (77262990844128679479/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree011.table
  base := (5424580630930673491122903437630480609259/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-1156765236896475368411074637000000000000)
      constant := (15464134178551832034716889152860961218518) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree011.table
  base := (5293438893295395503942562653006304446983/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-48040650503209719658637143259345000000000000)
      constant := (629564812470893205577929441951703599911444894) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree011.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel011

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154525981688257358957/100000000000000000000)
  centralHi := (77262990844128679479/50000000000000000000)
  directionLo := (16206821686682313061/10000000000000000000)
  directionHi := (162068216866823130611/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree012.table
  base := (8751216673776233168349615288902425530461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-1239951948930256425684959219000000000000)
      constant := (14085204746214737759049507723302425530461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree012.table
  base := (4258422488375766325590538750652542932689/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-51502465524495518357089850139275000000000000)
      constant := (574417981325024607650932090125221283426362002) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree012.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel012

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16206821686682313061/10000000000000000000)
  centralHi := (162068216866823130611/100000000000000000000)
  directionLo := (169274731782577574239/100000000000000000000)
  directionHi := (1057967073641109839/625000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree013.table
  base := (14031127687540704913239710096528517161283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-2646277321928074965917687602000000000000)
      constant := (26236958198354290439825776777328517161283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree013.table
  base := (544607031575033461881432590837059032969/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16483600000000000000000000000000000000000000
      center := (49938)
      previous := (0)
      next := (32480)
      square := (228536081080005572613300649309200000000000)
      linear := (-4397142443662505364443404561536400000000000)
      constant := (42898872807119544945231301337146765689619521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree013.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel013

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169274731782577574239/100000000000000000000)
  centralHi := (1057967073641109839/625000000000000000)
  directionLo := (176186726860270445307/100000000000000000000)
  directionHi := (44046681715067611327/25000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree014.table
  base := (11154411601553681471813538643904483846889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-2812650745995637080465456766000000000000)
      constant := (24997920532744380612314548635104483846889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree014.table
  base := (10787489554768498692572213215384537280757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (178350)
      previous := (0)
      next := (116000)
      square := (816200289571448473618930890390000000000000)
      linear := (-16693170162019175929712932542610000000000000)
      constant := (146378601677339542115953640597468770971816459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree014.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel014

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176186726860270445307/100000000000000000000)
  centralHi := (44046681715067611327/25000000000000000000)
  directionLo := (182837607245904167319/100000000000000000000)
  directionHi := (4570940181147604183/2500000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree015.table
  base := (8765688703201776701552925700584186196563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-2979024170063199195013225930000000000000)
      constant := (24346700109210126724697540500584186196563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree015.table
  base := (527729276879597194139301626800383498171/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-61887910588352914452447970779065000000000000)
      constant := (500481653253504200052928174168386028609029912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree015.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel015

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (182837607245904167319/100000000000000000000)
  centralHi := (4570940181147604183/2500000000000000000)
  directionLo := (189254903569443803541/100000000000000000000)
  directionHi := (94627451784721901771/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree016.table
  base := (1355509828459409450006068173388724796131/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (4)
      square := (27728904011260352424628194000000000000)
      linear := (-629079518826152261912199018800000000000)
      constant := (4839177415512717084909444394828724796131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree016.table
  base := (3248095887859642076141388214675667603873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-65349725609638713150900677658995000000000000)
      constant := (498902233219386181313410548294649586288002457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree016.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel016

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (189254903569443803541/100000000000000000000)
  centralHi := (94627451784721901771/50000000000000000000)
  directionLo := (195461623923345724853/100000000000000000000)
  directionHi := (97730811961672862427/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree017.table
  base := (1279579090354391755855796724216584929693/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-1655885509099161712054382129000000000000)
      constant := (12236902440191415309020497904833169859386) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree017.table
  base := (2436723696500677949985985059590367993719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-68811540630924511849353384538925000000000000)
      constant := (506111312220130975128897292510099474653166271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree017.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel017

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195461623923345724853/100000000000000000000)
  centralHi := (97730811961672862427/50000000000000000000)
  directionLo := (100738615148838782633/50000000000000000000)
  directionHi := (201477230297677565267/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree018.table
  base := (932303828251242851911827357368610640683/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-1739072221132942769328266711000000000000)
      constant := (12560839235054748845547353823137221281366) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree018.table
  base := (879210000549431667459212973060507855653/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-72273355652210310547806091418855000000000000)
      constant := (520901563814705732505964001571630936447208954) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree018.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel018

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100738615148838782633/50000000000000000000)
  centralHi := (201477230297677565267/100000000000000000000)
  directionLo := (1619674684428896113/781250000000000000)
  directionHi := (41463671921379740493/20000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree019.table
  base := (160128145062648792580693304909981733711/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-1822258933166723826602151293000000000000)
      constant := (13045656085343353461148370948879853869688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree019.table
  base := (2378425246490890422325855779901205033251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1248450)
      previous := (0)
      next := (812000)
      square := (5713402027000139315332516232730000000000000)
      linear := (-151470341346992218492517596597570000000000000)
      constant := (1084570237006128300505340868957048758215240459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree019.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel019

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1619674684428896113/781250000000000000)
  centralHi := (41463671921379740493/20000000000000000000)
  directionLo := (42599873301110806181/20000000000000000000)
  directionHi := (106499683252777015453/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree020.table
  base := (1577300878570663025222104066122568667221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-3810891290401009767752071750000000000000)
      constant := (27343185475275326492514665386122568667221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree020.table
  base := (1418973722427939612698856223542554884747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1248450)
      previous := (0)
      next := (812000)
      square := (5713402027000139315332516232730000000000000)
      linear := (-158393971389563815889423010357430000000000000)
      constant := (1138907348083521589726837348316565144245539123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree020.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel020

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42599873301110806181/20000000000000000000)
  centralHi := (106499683252777015453/50000000000000000000)
  directionLo := (218532739042550091863/100000000000000000000)
  directionHi := (27316592380318761483/12500000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree021.table
  base := (371280085154851112642605273673461250063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-1988632357234285941149920457000000000000)
      constant := (14422445784237620093796672833273461250063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree021.table
  base := (606386886328371674461820994554193446333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (178350)
      previous := (0)
      next := (116000)
      square := (816200289571448473618930890390000000000000)
      linear := (-23616800204590773326618346302470000000000000)
      constant := (171927387425008786059109266730420536818562371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree021.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel021

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218532739042550091863/100000000000000000000)
  centralHi := (27316592380318761483/12500000000000000000)
  directionLo := (223929421771930769443/100000000000000000000)
  directionHi := (55982355442982692361/25000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree022.table
  base := (15627319674453029305353925974534693181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-2071819069268066998423805039000000000000)
      constant := (15284928446707927892331539134374534693181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree022.table
  base := (-10699889293135556558720032682269612991/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-86120615737353505341616918938575000000000000)
      constant := (638620510790769817725550419075975406073015524) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree022.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel022

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223929421771930769443/100000000000000000000)
  centralHi := (55982355442982692361/25000000000000000000)
  directionLo := (45839814064537053689/20000000000000000000)
  directionHi := (114599535161342634223/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree023.table
  base := (-115681196341491399935602818006915726047/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (4)
      square := (27728904011260352424628194000000000000)
      linear := (-862002312520739222279075848400000000000)
      constant := (6499258236540288351769450624553084273953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree023.table
  base := (-169618503682588758148165064288486889719/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-89582430758639304040069625818505000000000000)
      constant := (679634853203828592702598877358801487523139458) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree023.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel023

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45839814064537053689/20000000000000000000)
  centralHi := (114599535161342634223/50000000000000000000)
  directionLo := (117175127201184629039/50000000000000000000)
  directionHi := (234350254402369258079/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree024.table
  base := (-220857930948755568345753730773234521813/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (4)
      square := (27728904011260352424628194000000000000)
      linear := (-895276997334251645188629681200000000000)
      constant := (6921265294889521443599611370666765478187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree024.table
  base := (-118982123159829052269385639453083416433/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 41209000000000000000000000000000000000000000
      center := (124845)
      previous := (0)
      next := (81200)
      square := (571340202700013931533251623273000000000000)
      linear := (-18608849155985020547704466539687000000000000)
      constant := (144885317143170417580232106505097885492212503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree024.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel024

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117175127201184629039/50000000000000000000)
  centralHi := (234350254402369258079/100000000000000000000)
  directionLo := (119695310726994602561/50000000000000000000)
  directionHi := (239390621453989205123/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree025.table
  base := (-780524024552464553266350719977757796033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-2321379205369410170245458785000000000000)
      constant := (18442655549654739761562171930022242203967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree025.table
  base := (-1634027925779569398664272581736045444283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1248450)
      previous := (0)
      next := (812000)
      square := (5713402027000139315332516232730000000000000)
      linear := (-193012121602421802873950079156730000000000000)
      constant := (1545398536143009177329481685821239303286541853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree025.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel025

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119695310726994602561/50000000000000000000)
  centralHi := (239390621453989205123/100000000000000000000)
  directionLo := (244327029904182156067/100000000000000000000)
  directionHi := (61081757476045539017/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree026.table
  base := (-78427819045867720736602434380862032221/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (4)
      square := (27728904011260352424628194000000000000)
      linear := (-961826366961276491007737346800000000000)
      constant := (7864246149186255289980173146335689838895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree026.table
  base := (-252858249762289853520151338016871667503/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-99967875822496700135427746458295000000000000)
      constant := (824210346140255366767344931817180941815475492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree026.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel026

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244327029904182156067/100000000000000000000)
  centralHi := (61081757476045539017/25000000000000000000)
  directionLo := (249165658635918538197/100000000000000000000)
  directionHi := (124582829317959269099/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree027.table
  base := (-1156541808979691213949475590269935384199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-2487752629436972284793227949000000000000)
      constant := (20952116866111342573902259100130064615801) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree027.table
  base := (-147872967383974124102143605086650811923/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-103429690843782498833880453338225000000000000)
      constant := (878761356768436899703025461379063653531720744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree027.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel027

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249165658635918538197/100000000000000000000)
  centralHi := (124582829317959269099/50000000000000000000)
  directionLo := (253912097673866361359/100000000000000000000)
  directionHi := (3173901220923329517/1250000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree028.table
  base := (-1313145403133793611049143718195190135479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-2570939341470753342067112531000000000000)
      constant := (22313120863229557864860693116204809864521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree028.table
  base := (-2671213501400608880331892023511014287843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (178350)
      previous := (0)
      next := (116000)
      square := (816200289571448473618930890390000000000000)
      linear := (-30540430247162370723523760062330000000000000)
      constant := (267482832314269600260064179621870658887468259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree028.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel028

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253912097673866361359/100000000000000000000)
  centralHi := (3173901220923329517/1250000000000000000)
  directionLo := (129285711939501474187/50000000000000000000)
  directionHi := (2068571391032023587/800000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree029.table
  base := (-290694123176115323996584295742370891453/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1000000000000000000000000000000000000000
      center := (3)
      previous := (0)
      next := (2)
      square := (13864452005630176212314097000000000000)
      linear := (-530825210700906879868199422600000000000)
      constant := (4748063053795072235669869649777629108547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree029.table
  base := (-117802103254412393577253989702768515179/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 568400000000000000000000000000000000000000
      center := (1722)
      previous := (0)
      next := (1120)
      square := (7880554520000192159079332734800000000000)
      linear := (-304422954169252679257340323029200000000000)
      constant := (2748587991002901410478942349680365939930641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree029.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel029

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129285711939501474187/50000000000000000000)
  centralHi := (2068571391032023587/800000000000000000)
  directionLo := (263148264574340259887/100000000000000000000)
  directionHi := (16446766535896266243/6250000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree030.table
  base := (-3160466695901056052663236069475154609281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-5474625531076630913229763390000000000000)
      constant := (50461968365236529457574830670524845390719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree030.table
  base := (-798190257103573992012503013049803682141/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-113815135907639894929238573978015000000000000)
      constant := (1059172341946797512270811123590411280125303062) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree030.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel030

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263148264574340259887/100000000000000000000)
  centralHi := (16446766535896266243/6250000000000000000)
  directionLo := (16727928210844981453/6250000000000000000)
  directionHi := (267646851373519703249/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree031.table
  base := (-1695660623620846585839600168340273567561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-2820499477572096513888766277000000000000)
      constant := (26782900579881069760430527593259726432439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree031.table
  base := (-854664007847983316442737603461178042691/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-117276950928925693627691280857945000000000000)
      constant := (1124528545207446182088398798243066628077493162) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree031.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel031

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16727928210844981453/6250000000000000000)
  centralHi := (267646851373519703249/100000000000000000000)
  directionLo := (272071065995322094859/100000000000000000000)
  directionHi := (13603553299766104743/5000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree032.table
  base := (-3603157182860637218450690782690087997187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-5807372379211755142325301718000000000000)
      constant := (56788476624449979925120415022109912002813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree032.table
  base := (-113320937694080187512489681673155811471/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-120738765950211492326143987737875000000000000)
      constant := (1192358972856728850785381098232334754641464976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree032.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel032

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272071065995322094859/100000000000000000000)
  centralHi := (13603553299766104743/5000000000000000000)
  directionLo := (276424479475864936619/100000000000000000000)
  directionHi := (13821223973793246831/5000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree033.table
  base := (-1899484684531329176275915771661481173969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-2986872901639658628436535441000000000000)
      constant := (30063499946497640255389393020738518826031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree033.table
  base := (-38184932521287732019580774669183368439/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8241800000000000000000000000000000000000000
      center := (24969)
      previous := (0)
      next := (16240)
      square := (114268040540002786306650324654600000000000)
      linear := (-4968023238859891640983867784712200000000000)
      constant := (50504162868942885069506865453350445139994498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree033.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel033

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276424479475864936619/100000000000000000000)
  centralHi := (13821223973793246831/5000000000000000000)
  directionLo := (280710385905428943477/100000000000000000000)
  directionHi := (140355192952714471739/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree034.table
  base := (-995303395957976033380573543090734870169/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-3070059613673439685710420023000000000000)
      constant := (31789457593706946859148248345418530259662) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree034.table
  base := (-3997690676376535435785970538820691880099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1248450)
      previous := (0)
      next := (812000)
      square := (5713402027000139315332516232730000000000000)
      linear := (-255324791985566179446098802995470000000000000)
      constant := (2670430228153911750773453123728638108313000309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree034.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel034

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280710385905428943477/100000000000000000000)
  centralHi := (140355192952714471739/50000000000000000000)
  directionLo := (284931831596343066973/100000000000000000000)
  directionHi := (142465915798171533487/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree035.table
  base := (-4151903557099878027160483307679894244777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-6306492651414441485968609210000000000000)
      constant := (67142208777774316081875142332320105755223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree035.table
  base := (-833159460164085567168036272514947263589/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11774000000000000000000000000000000000000000
      center := (35670)
      previous := (0)
      next := (23200)
      square := (163240057914289694723786178078000000000000)
      linear := (-7492812057946793624085834764438000000000000)
      constant := (80580127414790299964853275600684505459251557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree035.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel035

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (284931831596343066973/100000000000000000000)
  centralHi := (142465915798171533487/50000000000000000000)
  directionLo := (144545820208090737247/50000000000000000000)
  directionHi := (57818328083236294899/20000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree036.table
  base := (-4312690543230731010911225721317562335413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-6472866075482003600516378374000000000000)
      constant := (70815229409712396624069896193882437664587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree036.table
  base := (-864879281506187750698110303545827627227/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 82418000000000000000000000000000000000000000
      center := (249690)
      previous := (0)
      next := (162400)
      square := (1142680405400027863066503246546000000000000)
      linear := (-53834410414141874847981926103038000000000000)
      constant := (594953118413509548598595607580371989309602557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree036.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel036

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (144545820208090737247/50000000000000000000)
  centralHi := (57818328083236294899/20000000000000000000)
  directionLo := (3664905448562732341/1250000000000000000)
  directionHi := (293192435885018587281/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree037.table
  base := (-4464928569949821660400049744916934742501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-6639239499549565715064147538000000000000)
      constant := (74596623055502776769255229943883065257499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree037.table
  base := (-894956695812083309252806355270920316223/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 82418000000000000000000000000000000000000000
      center := (249690)
      previous := (0)
      next := (162400)
      square := (1142680405400027863066503246546000000000000)
      linear := (-55219136422656194327363008855010000000000000)
      constant := (626752048052614751995493036999216644688766393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree037.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel037

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3664905448562732341/1250000000000000000)
  centralHi := (293192435885018587281/100000000000000000000)
  directionLo := (148618330264021184009/50000000000000000000)
  directionHi := (297236660528042368019/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree038.table
  base := (-4609727941990885513705819575462346653283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-6805612923617127829611916702000000000000)
      constant := (78485279410411720979352279385337653346717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree038.table
  base := (-2309009257804316008794132773573688195211/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-141509656077926284516860229017455000000000000)
      constant := (1648622361278003097342438165038831883163549901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree038.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel038

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148618330264021184009/50000000000000000000)
  centralHi := (297236660528042368019/100000000000000000000)
  directionLo := (301226592889032067871/100000000000000000000)
  directionHi := (9413331027782252121/3125000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree039.table
  base := (-4747999113652954767592257177300836401341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-6971986347684689944159685866000000000000)
      constant := (82480288020140197057597322553899163598659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree039.table
  base := (-1188742210471904372546709801342081502589/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-144971471099212083215312935897385000000000000)
      constant := (1732591648681143453564047601104238326719619798) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree039.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel039

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301226592889032067871/100000000000000000000)
  centralHi := (9413331027782252121/3125000000000000000)
  directionLo := (76291090635312157341/25000000000000000000)
  directionHi := (61032872508249725873/20000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree040.table
  base := (-2440244331952932118585471660618248923141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-3569179885876126029353727515000000000000)
      constant := (43290451152859185094439389339381751076859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree040.table
  base := (-4886344132446923969704230478963985157201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1248450)
      previous := (0)
      next := (812000)
      square := (5713402027000139315332516232730000000000000)
      linear := (-296866572240995763827531285554630000000000000)
      constant := (3637546719703403449915518518697573135656903991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree040.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel040

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76291090635312157341/25000000000000000000)
  centralHi := (61032872508249725873/20000000000000000000)
  directionLo := (154525981688257358957/50000000000000000000)
  directionHi := (61810392675302943583/20000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree041.table
  base := (-1001561759125615044943514498636720331551/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (4)
      square := (27728904011260352424628194000000000000)
      linear := (-1460946639163962834651044838800000000000)
      constant := (18157302012853555814184190654803279668449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree041.table
  base := (-2506362534988907790951009684490827824917/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-151895101141783680612218349657245000000000000)
      constant := (1907155530113165759844318664640897476162995347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree041.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel041

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154525981688257358957/50000000000000000000)
  centralHi := (61810392675302943583/20000000000000000000)
  directionLo := (312891265407889837029/100000000000000000000)
  directionHi := (31289126540788983703/10000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree042.table
  base := (-513046152467391040066451390758800511103/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1000000000000000000000000000000000000000
      center := (3)
      previous := (0)
      next := (2)
      square := (13864452005630176212314097000000000000)
      linear := (-747110661988737628780299335800000000000)
      constant := (9509660927993410103329147712521199488897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree042.table
  base := (-5134586793991744073052498516251067223759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (178350)
      previous := (0)
      next := (116000)
      square := (816200289571448473618930890390000000000000)
      linear := (-44387690332305565517334587582050000000000000)
      constant := (570779534129563385919330960932169967253730767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree042.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel042

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312891265407889837029/100000000000000000000)
  centralHi := (31289126540788983703/10000000000000000000)
  directionLo := (63336805056845904723/20000000000000000000)
  directionHi := (9896375790132172613/3125000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree043.table
  base := (-2624429257319672628840252518565384642953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-3818740021977469201175381261000000000000)
      constant := (49755394144560680291660806379834615357047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree043.table
  base := (-2626159043441237727264174016298245200539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-158818731184355278009123763417105000000000000)
      constant := (2090483867205787645796449967849795613530988349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree043.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel043

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63336805056845904723/20000000000000000000)
  centralHi := (9896375790132172613/3125000000000000000)
  directionLo := (64086379136878840853/20000000000000000000)
  directionHi := (160215947842197102133/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree044.table
  base := (-5363337341136072835507502775954769275273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-7803853468022500516898531686000000000000)
      constant := (104028709516217864681269403283245230724727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree044.table
  base := (-2683118536118646753756535592171852194739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-162280546205641076707576470297035000000000000)
      constant := (2185415468592658956411297985351490142907000549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree044.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel044

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64086379136878840853/20000000000000000000)
  centralHi := (160215947842197102133/50000000000000000000)
  directionLo := (16206821686682313061/5000000000000000000)
  directionHi := (324136433733646261221/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree045.table
  base := (-1368543707073647689252575378138936960089/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-3985113446045031315723150425000000000000)
      constant := (54325048068546557852135027153722126079822) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree045.table
  base := (-547660405940968005558715825258235924061/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 41209000000000000000000000000000000000000000
      center := (124845)
      previous := (0)
      next := (81200)
      square := (571340202700013931533251623273000000000000)
      linear := (-33148472245385375081205835435393000000000000)
      constant := (456503562014002393265647640754193355805370251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree045.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel045

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16206821686682313061/5000000000000000000)
  centralHi := (324136433733646261221/100000000000000000000)
  directionLo := (163899554281912568897/50000000000000000000)
  directionHi := (65559821712765027559/20000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree046.table
  base := (-1116319596904812074247388241476558016527/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (4)
      square := (27728904011260352424628194000000000000)
      linear := (-1627320063231524949198814002800000000000)
      constant := (22674944228667590460655105174363441983473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree046.table
  base := (-348977003319756740925897818412120238183/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-169204176248212674104481884056895000000000000)
      constant := (2381786502782166112644954965546869496837734024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree046.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel046

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163899554281912568897/50000000000000000000)
  centralHi := (65559821712765027559/20000000000000000000)
  directionLo := (331421308121415729309/100000000000000000000)
  directionHi := (33142130812141572931/10000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree047.table
  base := (-5685792969688510024321809773264329289867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-8302973740225186860541839178000000000000)
      constant := (118202398375088346132151430063535670710133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree047.table
  base := (-1137499070503843796483813231722649214371/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 82418000000000000000000000000000000000000000
      center := (249690)
      previous := (0)
      next := (162400)
      square := (1142680405400027863066503246546000000000000)
      linear := (-69066396507799389121173836374730000000000000)
      constant := (993287182152809894672511458944217348524985461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree047.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel047

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331421308121415729309/100000000000000000000)
  centralHi := (33142130812141572931/10000000000000000000)
  directionLo := (335004345312985975477/100000000000000000000)
  directionHi := (167502172656492987739/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree048.table
  base := (-5786912448067211898692809638858467658651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-8469347164292748975089608342000000000000)
      constant := (123132975168065025008469864453941532341349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree048.table
  base := (-2894168293550370776308501605699443013949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-176127806290784271501387297816755000000000000)
      constant := (2586809229060431571507850997978811652838175659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree048.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel048

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335004345312985975477/100000000000000000000)
  centralHi := (167502172656492987739/50000000000000000000)
  directionLo := (338549463565155148479/100000000000000000000)
  directionHi := (1057967073641109839/312500000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree049.table
  base := (-5885081617678044710013264035542973337967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-8635720588360311089637377506000000000000)
      constant := (128166326324250110216567505811657026662033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree049.table
  base := (-5886272473494214169118029061586068753417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (178350)
      previous := (0)
      next := (116000)
      square := (816200289571448473618930890390000000000000)
      linear := (-51311320374877162914240001341910000000000000)
      constant := (769302262551288820275580672916042813248634121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree049.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel049

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338549463565155148479/100000000000000000000)
  centralHi := (1057967073641109839/312500000000000000)
  directionLo := (171028920932927509247/50000000000000000000)
  directionHi := (68411568373171003699/20000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree050.table
  base := (-2990201577117948661117450118701681823941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-4401047006213936602092573335000000000000)
      constant := (66651174583964356446246313431298318176059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree050.table
  base := (-373837407861905069522716253782827761439/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-183051436333355868898292711576615000000000000)
      constant := (2800462056969177834074969616281157606230881992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree050.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel050

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171028920932927509247/50000000000000000000)
  centralHi := (68411568373171003699/20000000000000000000)
  directionLo := (172765299672415585387/50000000000000000000)
  directionHi := (13821223973793246831/4000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree051.table
  base := (-1214592253025374578791839376928045063239/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (4)
      square := (27728904011260352424628194000000000000)
      linear := (-1793693487299087063746583166800000000000)
      constant := (27708191898342945975528749793311954936761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree051.table
  base := (-6073792909561939261329475942277126345711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1248450)
      previous := (0)
      next := (812000)
      square := (5713402027000139315332516232730000000000000)
      linear := (-373026502709283335193490836913090000000000000)
      constant := (5821040065233792018692596171746761900419595401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree051.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel051

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172765299672415585387/50000000000000000000)
  centralHi := (13821223973793246831/4000000000000000000)
  directionLo := (2791750395550664789/800000000000000000)
  directionHi := (174484399721916549313/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree052.table
  base := (-6162825013608433836737234950880334632289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-9134840860562997433280684998000000000000)
      constant := (143882088232350698760469791149919665367711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree052.table
  base := (-1232703919053556964145052801386787550821/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 82418000000000000000000000000000000000000000
      center := (249690)
      previous := (0)
      next := (162400)
      square := (1142680405400027863066503246546000000000000)
      linear := (-75990026550370986518079250134590000000000000)
      constant := (1209092211117335555431434925703227871818217411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree052.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel052

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2791750395550664789/800000000000000000)
  centralHi := (174484399721916549313/50000000000000000000)
  directionLo := (176186726860270445307/50000000000000000000)
  directionHi := (70474690744108178123/20000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree053.table
  base := (-6250051044605953049820765621477320684317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-9301214284630559547828454162000000000000)
      constant := (149325678744911246641719002227322679315683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree053.table
  base := (-781328867300675691490214049158141107811/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-193436881397213264993650832216405000000000000)
      constant := (3137092463739660546054760836779948652352866004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree053.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel053

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176186726860270445307/50000000000000000000)
  centralHi := (70474690744108178123/20000000000000000000)
  directionLo := (355745525324794686571/100000000000000000000)
  directionHi := (88936381331198671643/25000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree054.table
  base := (-1583671454956955532300948945792366683007/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-4733793854349060831188111663000000000000)
      constant := (77435842283843990962698687656015266633986) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree054.table
  base := (-1267033958123967376310072777257677223583/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 82418000000000000000000000000000000000000000
      center := (249690)
      previous := (0)
      next := (162400)
      square := (1142680405400027863066503246546000000000000)
      linear := (-78759478567399625476841415638534000000000000)
      constant := (1301441983007656339236207612050048379293368153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree054.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel054

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (355745525324794686571/100000000000000000000)
  centralHi := (88936381331198671643/25000000000000000000)
  directionLo := (359085932180983807683/100000000000000000000)
  directionHi := (89771483045245951921/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree055.table
  base := (-1283353490105970144119477326556520363507/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (4)
      square := (27728904011260352424628194000000000000)
      linear := (-1926792226553136755384798498000000000000)
      constant := (32104013517885018993158769841443479636493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree055.table
  base := (-6417171227038813277608527205010113056389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1248450)
      previous := (0)
      next := (812000)
      square := (5713402027000139315332516232730000000000000)
      linear := (-400721022879569724781112491952530000000000000)
      constant := (6744534572852620782152562693585638251059265699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree055.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel055

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359085932180983807683/100000000000000000000)
  centralHi := (89771483045245951921/25000000000000000000)
  directionLo := (181197774953197250493/50000000000000000000)
  directionHi := (362395549906394500987/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree056.table
  base := (-259853088014356523346622601542076794523/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (4)
      square := (27728904011260352424628194000000000000)
      linear := (-1960066911366649178294352330800000000000)
      constant := (33254159309295142300648879408929616027385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree056.table
  base := (-6496663959600324880022794791847378382271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (178350)
      previous := (0)
      next := (116000)
      square := (816200289571448473618930890390000000000000)
      linear := (-58234950417448760311145415101770000000000000)
      constant := (998022531104583673360525803658074483463570623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree056.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel056

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181197774953197250493/50000000000000000000)
  centralHi := (362395549906394500987/100000000000000000000)
  directionLo := (365675214491808334639/100000000000000000000)
  directionHi := (4570940181147604183/1250000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree057.table
  base := (-6573390717667325067465228490538568106537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-9966707980900808006019530818000000000000)
      constant := (172123845790487515688692121334261431893463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree057.table
  base := (-3286835746728367432270862911617575184769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-207284141482356459787461659736125000000000000)
      constant := (3616039190526426378092484740605591344210854279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree057.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel057

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (365675214491808334639/100000000000000000000)
  centralHi := (4570940181147604183/1250000000000000000)
  directionLo := (720558056186726821/195312500000000000)
  directionHi := (368925724767604132353/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree058.table
  base := (-3323989522999017181325133651871179093487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-5066540702484185060283649991000000000000)
      constant := (89039597138958779915741565880528820906513) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree058.table
  base := (-6648213073162208513528654230359241714817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14210000000000000000000000000000000000000000
      center := (43050)
      previous := (0)
      next := (28000)
      square := (197013863000004803976983318370000000000000)
      linear := (-14534203896802914378338921835590000000000000)
      constant := (258010198957451355621224780428599517523245043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree058.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel058

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (720558056186726821/195312500000000000)
  centralHi := (368925724767604132353/100000000000000000000)
  directionLo := (372147844675975467349/100000000000000000000)
  directionHi := (7442956893519509347/2000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree059.table
  base := (-3360054726336944608051653382214965844403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-5149727414517966117557534573000000000000)
      constant := (92068412370721497842367401519385034155597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree059.table
  base := (-52502378569213672771847080502888201257/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-214207771524928057184367073495985000000000000)
      constant := (3868404617247248401959424248224564727321618368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree059.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel059

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (372147844675975467349/100000000000000000000)
  centralHi := (7442956893519509347/2000000000000000000)
  directionLo := (75068461073515001653/20000000000000000000)
  directionHi := (187671152683787504133/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree060.table
  base := (-6789796108235575255236074781619476736331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-10465828253103494349662838310000000000000)
      constant := (190296723010523137621035407258380523263669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree060.table
  base := (-3394979274866807402917164922886815151897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-217669586546213855882819780375915000000000000)
      constant := (3997809121714143904067081506149657234405476527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree060.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel060

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75068461073515001653/20000000000000000000)
  centralHi := (187671152683787504133/50000000000000000000)
  directionLo := (378509807138887607083/100000000000000000000)
  directionHi := (94627451784721901771/25000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree061.table
  base := (-68570506435781967665871258864270408407/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1000000000000000000000000000000000000000
      center := (3)
      previous := (0)
      next := (2)
      square := (13864452005630176212314097000000000000)
      linear := (-1063220167717105646421060747400000000000)
      constant := (19655887745426288135384638988877295915930) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree061.table
  base := (-6857185922319674045518926066506993458733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1248450)
      previous := (0)
      next := (812000)
      square := (5713402027000139315332516232730000000000000)
      linear := (-442262803134999309162544974511690000000000000)
      constant := (8258722360966299049512617968997273306559071803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree061.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel061

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (378509807138887607083/100000000000000000000)
  centralHi := (94627451784721901771/25000000000000000000)
  directionLo := (190825510612437414083/50000000000000000000)
  directionHi := (381651021224874828167/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree062.table
  base := (-6921882606802983540325789625890958844581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-10798575101238618578758376638000000000000)
      constant := (202923278524560997092998421382909041155419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree062.table
  base := (-692199523459288354530596662904103282713/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 41209000000000000000000000000000000000000000
      center := (124845)
      previous := (0)
      next := (81200)
      square := (571340202700013931533251623273000000000000)
      linear := (-44918643317757090655945038827155000000000000)
      constant := (852612123023960609454083329628422807822679983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree062.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel062

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190825510612437414083/50000000000000000000)
  centralHi := (381651021224874828167/100000000000000000000)
  directionLo := (384766591459889902753/100000000000000000000)
  directionHi := (192383295729944951377/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree063.table
  base := (-6984299837837214351542716435234778445897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-10964948525306180693306145802000000000000)
      constant := (209389918381490206063400851305565221554103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree063.table
  base := (-6984393582973482614159162819669945426957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (178350)
      previous := (0)
      next := (116000)
      square := (816200289571448473618930890390000000000000)
      linear := (-65158580460020357708050828861630000000000000)
      constant := (1256830651258832471647960487966183031271504141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree063.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel063

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (384766591459889902753/100000000000000000000)
  centralHi := (192383295729944951377/50000000000000000000)
  directionLo := (387857135818504422561/100000000000000000000)
  directionHi := (193928567909252211281/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree064.table
  base := (-7044308775625534024389954440673782633273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-11131321949373742807853914966000000000000)
      constant := (215958790586105863440901631530526217366727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree064.table
  base := (-7044386784257442462505300950155126252239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1248450)
      previous := (0)
      next := (812000)
      square := (5713402027000139315332516232730000000000000)
      linear := (-463033693262714101353261215791270000000000000)
      constant := (9073802106978617492886810890313057402271483049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree064.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel064

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387857135818504422561/100000000000000000000)
  centralHi := (193928567909252211281/50000000000000000000)
  directionLo := (390923247846691449707/100000000000000000000)
  directionHi := (97730811961672862427/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree065.table
  base := (-7101914710030968012394974979586977722419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-11297695373441304922401684130000000000000)
      constant := (222629889848544943771973290720413022277581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree065.table
  base := (-7101979607940216585177016382248440878917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1248450)
      previous := (0)
      next := (812000)
      square := (5713402027000139315332516232730000000000000)
      linear := (-469957323305285698750166629551130000000000000)
      constant := (9354083678193838525525537649311123999820709347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree065.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel065

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390923247846691449707/100000000000000000000)
  centralHi := (97730811961672862427/25000000000000000000)
  directionLo := (615571090613676261/156250000000000000)
  directionHi := (393965497992752807041/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree066.table
  base := (-357856099419939554899783169370857235817/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1000000000000000000000000000000000000000
      center := (3)
      previous := (0)
      next := (2)
      square := (13864452005630176212314097000000000000)
      linear := (-1146406879750886703694945329400000000000)
      constant := (22940321182146217227417794353978285528366) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree066.table
  base := (-7157175966315128596893245966652209857889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1248450)
      previous := (0)
      next := (812000)
      square := (5713402027000139315332516232730000000000000)
      linear := (-476880953347857296147072043310990000000000000)
      constant := (9638659111235794826612951024076889083966252199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree066.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel066

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (615571090613676261/156250000000000000)
  centralHi := (393965497992752807041/100000000000000000000)
  directionLo := (198492217423221458211/50000000000000000000)
  directionHi := (396984434846442916423/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree067.table
  base := (-450620886559039220270050187933790890241/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-5815221110788214575748611229000000000000)
      constant := (118139376465320962352193403322929672878072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree067.table
  base := (-72099790700225670539923323637146279317/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8241800000000000000000000000000000000000000
      center := (24969)
      previous := (0)
      next := (16240)
      square := (114268040540002786306650324654600000000000)
      linear := (-9676091667808577870879549141417000000000000)
      constant := (198550565475944132482618085038401277951251494) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree067.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel067

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198492217423221458211/50000000000000000000)
  centralHi := (396984434846442916423/100000000000000000000)
  directionLo := (39998058629391207711/10000000000000000000)
  directionHi := (399980586293912077111/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree068.table
  base := (-1815088559914734066539327045819025683807/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-5898407822821995633022495811000000000000)
      constant := (121628255118046871043906482846761948632386) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree068.table
  base := (-907548944416331669946212328594105420241/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-245364106716500245470441435415355000000000000)
      constant := (5110345528620050451589619022077042038949154524) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree068.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel068

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39998058629391207711/10000000000000000000)
  centralHi := (399980586293912077111/100000000000000000000)
  directionLo := (402954460595355130533/100000000000000000000)
  directionHi := (201477230297677565267/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree069.table
  base := (-7308384572215301905942293192223067625289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-11963189069711553380592760786000000000000)
      constant := (250336481318144039842019306406976932374711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree069.table
  base := (-456775974267890087337188560073183136243/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-248825921737786044168894142295285000000000000)
      constant := (5259073686151926431030843989556853569108497704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree069.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel069

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402954460595355130533/100000000000000000000)
  centralHi := (201477230297677565267/50000000000000000000)
  directionLo := (405906547391595514629/100000000000000000000)
  directionHi := (40590654739159551463/10000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree070.table
  base := (-18385067938455239660608577523167931213/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1000000000000000000000000000000000000000
      center := (3)
      previous := (0)
      next := (2)
      square := (13864452005630176212314097000000000000)
      linear := (-1212956249377911549514052995000000000000)
      constant := (25751866418402444654643815581073282751480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree070.table
  base := (-7354052949940876286512216295703025412883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (178350)
      previous := (0)
      next := (116000)
      square := (816200289571448473618930890390000000000000)
      linear := (-72082210502591955104956242621490000000000000)
      constant := (1545699592227587053995367541332496289394357779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree070.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel070

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405906547391595514629/100000000000000000000)
  centralHi := (40590654739159551463/10000000000000000000)
  directionLo := (102209329661312456293/25000000000000000000)
  directionHi := (408837318645249825173/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree071.table
  base := (-7397283691627052649497330655545965010823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-12295935917846677609688299114000000000000)
      constant := (264803057191267227692632904883654034989177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree071.table
  base := (-1849326276522987197614312161520568191091/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-255749551780357641565799556055145000000000000)
      constant := (5562970158351912887461169714130727810826661962) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree071.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel071

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102209329661312456293/25000000000000000000)
  centralHi := (408837318645249825173/100000000000000000000)
  directionLo := (411747229521595573303/100000000000000000000)
  directionHi := (51468403690199446663/12500000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree072.table
  base := (-3719077737970053772042464482388636524447/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-6231154670957119862118034139000000000000)
      constant := (136094829492441223999111308396011363475553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree072.table
  base := (-1859543316088463892873174646797296668703/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-259211366801643440264252262935075000000000000)
      constant := (5718138417935710190435404524084700403158836146) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree072.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel072

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411747229521595573303/100000000000000000000)
  centralHi := (51468403690199446663/12500000000000000000)
  directionLo := (414636719213797404929/100000000000000000000)
  directionHi := (41463671921379740493/10000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree073.table
  base := (-7476643647355214908239050477753512459101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-12628682765981801838783837442000000000000)
      constant := (279678468445836153102974466995046487540899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree073.table
  base := (-7476658420862250670818878632838634660023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1248450)
      previous := (0)
      next := (812000)
      square := (5713402027000139315332516232730000000000000)
      linear := (-525346363645858477925409939630010000000000000)
      constant := (11750906662046139028429157970669512704295112193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree073.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel073

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414636719213797404929/100000000000000000000)
  centralHi := (41463671921379740493/10000000000000000000)
  directionLo := (8350124234334563119/2000000000000000000)
  directionHi := (417506211716728155951/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree074.table
  base := (-7512749131205284806545089257819678355153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-12795056190049363953331606606000000000000)
      constant := (287269484648795432942303061429380321644847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree074.table
  base := (-1878190349623944975496561246897482125071/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-266134996844215037661157676694935000000000000)
      constant := (6034914880658987801133392723014053318215898322) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree074.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel074

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8350124234334563119/2000000000000000000)
  centralHi := (417506211716728155951/100000000000000000000)
  directionLo := (26272257284577820283/6250000000000000000)
  directionHi := (420356116553245124529/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree075.table
  base := (-1886618173444547400670576644713130864029/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-6480714807058463033939687885000000000000)
      constant := (147481353413736207576264569410573738271942) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree075.table
  base := (-1886620719539278637129952254458808911141/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-269596811865500836359610383574865000000000000)
      constant := (6196523052813805960730454640423763887161581062) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree075.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel075

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26272257284577820283/6250000000000000000)
  centralHi := (420356116553245124529/100000000000000000000)
  directionLo := (423186829456443935599/100000000000000000000)
  directionHi := (1057967073641109839/250000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree076.table
  base := (-151556299414830571263126503285911869431/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1000000000000000000000000000000000000000
      center := (3)
      previous := (0)
      next := (2)
      square := (13864452005630176212314097000000000000)
      linear := (-1312780303818448818242714493400000000000)
      constant := (30275813434619950046714707644690440652845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree076.table
  base := (-7577823424374805740488559245093244482007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1248450)
      previous := (0)
      next := (812000)
      square := (5713402027000139315332516232730000000000000)
      linear := (-546117253773573270116126180909590000000000000)
      constant := (12720555671711390922492516527144512488140973537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree076.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel076

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423186829456443935599/100000000000000000000)
  centralHi := (1057967073641109839/250000000000000000)
  directionLo := (425998733011108061811/100000000000000000000)
  directionHi := (106499683252777015453/25000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree077.table
  base := (-7606776490457629802365050291693398345719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-13294176462252050296974914098000000000000)
      constant := (310655766676614360771758969029106601654281) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree077.table
  base := (-7606783506258143706900263388815287284373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (178350)
      previous := (0)
      next := (116000)
      square := (816200289571448473618930890390000000000000)
      linear := (-79005840545163552501861656381350000000000000)
      constant := (1864622634319683980616346583566884403756896149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree077.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel077

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (425998733011108061811/100000000000000000000)
  centralHi := (106499683252777015453/25000000000000000000)
  directionLo := (214396098628648846023/50000000000000000000)
  directionHi := (428792197257297692047/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree078.table
  base := (-7633357693108383925811952698401092956197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-13460549886319612411522683262000000000000)
      constant := (318655603378535105460861345830398907043803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree078.table
  base := (-954170439331195334313455615197952951121/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-279982256929358232454968504214655000000000000)
      constant := (6694227197550288437438192486368460227349018844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree078.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel078

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214396098628648846023/50000000000000000000)
  centralHi := (428792197257297692047/100000000000000000000)
  directionLo := (107891895064693477199/25000000000000000000)
  directionHi := (431567580258773908797/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree079.table
  base := (-1914389736595990782890578783123406124073/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-6813461655193587263035226213000000000000)
      constant := (163378822042135781168194462051353187751854) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree079.table
  base := (-239298868005175080903307309634173745291/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-283444071950644031153421211094585000000000000)
      constant := (6864421761420108479780181737803215346084850896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree079.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel079

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107891895064693477199/25000000000000000000)
  centralHi := (431567580258773908797/100000000000000000000)
  directionLo := (54290653579841269273/12500000000000000000)
  directionHi := (86865045727746030837/20000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree080.table
  base := (-7679380558353740412688148012455910863121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-13793296734454736640618221590000000000000)
      constant := (334961888485754358405269693427544089136879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree080.table
  base := (-7679384564691821151625635361707730868203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1248450)
      previous := (0)
      next := (812000)
      square := (5713402027000139315332516232730000000000000)
      linear := (-573811773943859659703747835949030000000000000)
      constant := (14073525812170158171043978649805786118652222573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree080.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel080

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54290653579841269273/12500000000000000000)
  centralHi := (86865045727746030837/20000000000000000000)
  directionLo := (218532739042550091863/50000000000000000000)
  directionHi := (437065478085100183727/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree081.table
  base := (-1924705697006605208390511965911082219987/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-6979835079261149377582995377000000000000)
      constant := (171634168161987394301565528639777835560026) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree081.table
  base := (-7698826110794269469877066822095966643189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1248450)
      previous := (0)
      next := (812000)
      square := (5713402027000139315332516232730000000000000)
      linear := (-580735403986431257100653249708890000000000000)
      constant := (14422501253589004109250212882518007310600824499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree081.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel081

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218532739042550091863/50000000000000000000)
  centralHi := (437065478085100183727/100000000000000000000)
  directionLo := (439788653827527880921/100000000000000000000)
  directionHi := (219894326913763940461/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree082.table
  base := (-3857942927007565714076551330569635871779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-7063021791294930434856879959000000000000)
      constant := (175838493690159862948001963841830364128221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree082.table
  base := (-3857944304713024999022755894313183325501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-293829517014501427248779331734375000000000000)
      constant := (7387884919531466187568149452562938028339429291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree082.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel082

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (439788653827527880921/100000000000000000000)
  centralHi := (219894326913763940461/50000000000000000000)
  directionLo := (88499014217583490253/20000000000000000000)
  directionHi := (221247535543958725633/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree083.table
  base := (-1932642485412095212037454296706805466147/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-7146208503328711492130764541000000000000)
      constant := (180093920734730330816099899928986389067706) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree083.table
  base := (-3865286113119334659641512946266020577099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-297291332035787225947232038614305000000000000)
      constant := (7566665780882805016958561828560953558038327309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree083.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel083

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88499014217583490253/20000000000000000000)
  centralHi := (221247535543958725633/50000000000000000000)
  directionLo := (222592517753165438441/50000000000000000000)
  directionHi := (445185035506330876883/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree084.table
  base := (-61943001670451492995388066098188757961/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (4)
      square := (27728904011260352424628194000000000000)
      linear := (-2891758086144997019761859649200000000000)
      constant := (73760179686703465656169471396185281050975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree084.table
  base := (-7742877102751601170746532790289345495711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (178350)
      previous := (0)
      next := (116000)
      square := (816200289571448473618930890390000000000000)
      linear := (-85929470587735149898767070141210000000000000)
      constant := (2213598059409308727479741067363766623066749343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree084.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel084

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222592517753165438441/50000000000000000000)
  centralHi := (445185035506330876883/100000000000000000000)
  directionLo := (223929421771930769443/50000000000000000000)
  directionHi := (447858843543861538887/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree085.table
  base := (-1550560358142470287320452540192399727951/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (4)
      square := (27728904011260352424628194000000000000)
      linear := (-2925032770958509442671413482000000000000)
      constant := (75503231627453334632463702447807600272049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree085.table
  base := (-3876401680293706386231918899501960582763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-304214962078358823344137452374165000000000000)
      constant := (7930667198174820588944682259543323706344919533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree085.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel085

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223929421771930769443/50000000000000000000)
  centralHi := (447858843543861538887/100000000000000000000)
  directionLo := (450516782863987224927/100000000000000000000)
  directionHi := (14078649464499600779/3125000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree086.table
  base := (-7760349803865611380359333635029354680361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-14791537278860109327904836574000000000000)
      constant := (386333620464209210180940012500170645319639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree086.table
  base := (-970043888117764905498018199354051398739/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-307676777099644622042590159254095000000000000)
      constant := (8115887749442013851724575812121505583637458196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree086.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel086

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (450516782863987224927/100000000000000000000)
  centralHi := (14078649464499600779/3125000000000000000)
  directionLo := (7080611448340486081/1562500000000000000)
  directionHi := (90631826538758221837/20000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree087.table
  base := (-388275967463627408682883888205502176861/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1000000000000000000000000000000000000000
      center := (3)
      previous := (0)
      next := (2)
      square := (13864452005630176212314097000000000000)
      linear := (-1495791070292767144245260573800000000000)
      constant := (39525328531333860761874890106468995646278) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree087.table
  base := (-3882760213714797118996447783159944283293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7105000000000000000000000000000000000000000
      center := (21525)
      previous := (0)
      next := (14000)
      square := (98506931500002401988491659185000000000000)
      linear := (-10728916969687255887622167797725000000000000)
      constant := (286319133098155250856621284745739719173440647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree087.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel087

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7080611448340486081/1562500000000000000)
  centralHi := (90631826538758221837/20000000000000000000)
  directionLo := (227893082083167315589/50000000000000000000)
  directionHi := (455786164166334631179/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree088.table
  base := (-1553662103019983283416776927348568263627/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (4)
      square := (27728904011260352424628194000000000000)
      linear := (-3024856825399046711400074980400000000000)
      constant := (80855030519297622175031717676811431736373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree088.table
  base := (-7768311408413634225526709236515305161741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1248450)
      previous := (0)
      next := (812000)
      square := (5713402027000139315332516232730000000000000)
      linear := (-629200814284432438878991146027910000000000000)
      constant := (16985537055464860027819065055773000789589815131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree088.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel088

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227893082083167315589/50000000000000000000)
  centralHi := (455786164166334631179/100000000000000000000)
  directionLo := (458398140645370536891/100000000000000000000)
  directionHi := (114599535161342634223/25000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree089.table
  base := (-1942180844713822501734097064326452028713/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-7645328775531397835774072033000000000000)
      constant := (206699611118075073026935320226947095942574) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree089.table
  base := (-155374482378412598791058840397716680833/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8241800000000000000000000000000000000000000
      center := (24969)
      previous := (0)
      next := (16240)
      square := (114268040540002786306650324654600000000000)
      linear := (-12722488886540080725517931195755400000000000)
      constant := (347377150065453352042787829930570493299552903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree089.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel089

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (458398140645370536891/100000000000000000000)
  centralHi := (114599535161342634223/25000000000000000000)
  directionLo := (230497659016748406933/50000000000000000000)
  directionHi := (460995318033496813867/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree090.table
  base := (-1941689502294819891550037422404229947969/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-7728515487565178893047956615000000000000)
      constant := (211312747081842051265950048105191540104062) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree090.table
  base := (-1941689655552226855891701859775417511749/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-321524037184787816836400986773815000000000000)
      constant := (8878235530254807457359309791731879639516670918) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree090.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel090

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230497659016748406933/50000000000000000000)
  centralHi := (460995318033496813867/100000000000000000000)
  directionLo := (57947243133096509609/12500000000000000000)
  directionHi := (463577945064772076873/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree091.table
  base := (-7762414467319278132419043881405351343909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-15623404399197919900643682394000000000000)
      constant := (431953968317842587271703080705794648656091) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree091.table
  base := (-121287733985265322631210110338901645349/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 29435000000000000000000000000000000000000000
      center := (89175)
      previous := (0)
      next := (58000)
      square := (408100144785724236809465445195000000000000)
      linear := (-46426550315153373647836241950535000000000000)
      constant := (1296312694631136870238060801551606352442573984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree091.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel091

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57947243133096509609/12500000000000000000)
  centralHi := (463577945064772076873/100000000000000000000)
  directionLo := (116536565895684862303/25000000000000000000)
  directionHi := (466146263582739449213/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree092.table
  base := (-7755692808341900860915737417414425020537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-15789777823265482015191451558000000000000)
      constant := (441384644643558985117956927355385574979463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree092.table
  base := (-1938923307205412376909629234698486548443/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-328447667227359414233306400533675000000000000)
      constant := (9272288747067604520583492719546560135650424826) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree092.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel092

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116536565895684862303/25000000000000000000)
  centralHi := (466146263582739449213/100000000000000000000)
  directionLo := (468700508804738516157/100000000000000000000)
  directionHi := (234350254402369258079/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree093.table
  base := (-3873296541065500263188470892969916824181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-7978075623666522064869610361000000000000)
      constant := (225458761545474721647987462335430083175819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree093.table
  base := (-1936648357576906106807089002727426372097/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-331909482248645212931759107413605000000000000)
      constant := (9472535183239359088139264613088390973264509454) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree093.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel093

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468700508804738516157/100000000000000000000)
  centralHi := (234350254402369258079/50000000000000000000)
  directionLo := (58905113696665368037/12500000000000000000)
  directionHi := (471240909573322944297/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree094.table
  base := (-7735115334209707725624817834968227171629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-16122524671400606244286989886000000000000)
      constant := (460552603614490831208934911804231772828371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree094.table
  base := (-7735115622482788116197282358539887448881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1248450)
      previous := (0)
      next := (812000)
      square := (5713402027000139315332516232730000000000000)
      linear := (-670742594539862023260423628587070000000000000)
      constant := (19349856340095780110111052205194029778119062871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree094.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel094

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58905113696665368037/12500000000000000000)
  centralHi := (471240909573322944297/100000000000000000000)
  directionLo := (473767688595544363799/100000000000000000000)
  directionHi := (2368838442977721819/500000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree095.table
  base := (-7721259606418029655880324730529708693093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-16288898095468168358834759050000000000000)
      constant := (470289886172343141659615929589470291306907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree095.table
  base := (-7721259845067010375806504443286579912047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1248450)
      previous := (0)
      next := (812000)
      square := (5713402027000139315332516232730000000000000)
      linear := (-677666224582433620657329042346930000000000000)
      constant := (19758935413349578728024381236650703328404455177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree095.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel095

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473767688595544363799/100000000000000000000)
  centralHi := (2368838442977721819/500000000000000000)
  directionLo := (29767566416925665617/6250000000000000000)
  directionHi := (476281062670810649873/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree096.table
  base := (-1541005187494374183342808442752291710803/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (4)
      square := (27728904011260352424628194000000000000)
      linear := (-3291054303907146094676505642800000000000)
      constant := (96025874145158094009689479657087708289197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree096.table
  base := (-770502613501736319682192158437681727073/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 41209000000000000000000000000000000000000000
      center := (124845)
      previous := (0)
      next := (81200)
      square := (571340202700013931533251623273000000000000)
      linear := (-68458985462500521805423445610679000000000000)
      constant := (2017230758471715005035104437550077573709048743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree096.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel096

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29767566416925665617/6250000000000000000)
  centralHi := (476281062670810649873/100000000000000000000)
  directionLo := (119695310726994602561/25000000000000000000)
  directionHi := (95756248581595682049/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree097.table
  base := (-1537282872684937980860490014774819758521/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (4)
      square := (27728904011260352424628194000000000000)
      linear := (-3324328988720658517586059475600000000000)
      constant := (98014211447755871595850567620585180241479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree097.table
  base := (-1537282905385687183478510541134358991099/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 82418000000000000000000000000000000000000000
      center := (249690)
      previous := (0)
      next := (162400)
      square := (1142680405400027863066503246546000000000000)
      linear := (-138302696933515363090227973973330000000000000)
      constant := (4117994570554577129011051740182170200335801309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree097.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel097

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119695310726994602561/25000000000000000000)
  centralHi := (95756248581595682049/20000000000000000000)
  directionLo := (481268434932294922493/100000000000000000000)
  directionHi := (240634217466147461247/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree098.table
  base := (-958178114756148914346346870207953749483/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (10)
      square := (69322260028150881061570485000000000000)
      linear := (-8394009183835427351239033271000000000000)
      constant := (250057472838768550377953511195568185002068) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree098.table
  base := (-7665425053363056509736248583309387375159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (178350)
      previous := (0)
      next := (116000)
      square := (816200289571448473618930890390000000000000)
      linear := (-99776730672878344692577897660930000000000000)
      constant := (3001704459453557704889985542892437636522438967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree098.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel098

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481268434932294922493/100000000000000000000)
  centralHi := (240634217466147461247/50000000000000000000)
  directionLo := (120935709770690909771/25000000000000000000)
  directionHi := (96748567816552727817/20000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree099.table
  base := (-7642057633153328405641361159170275002929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-16954391791738416817025835706000000000000)
      constant := (510261036010255745120887606868029724997071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree099.table
  base := (-955257218140743510534492650412542541179/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-352680372376360005122475348693185000000000000)
      constant := (10719091336826886541608773034648948137682218356) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree099.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel099

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120935709770690909771/25000000000000000000)
  centralHi := (96748567816552727817/20000000000000000000)
  directionLo := (486204650600469391831/100000000000000000000)
  directionHi := (60775581325058673979/12500000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree100.table
  base := (-7616312538842324457550208154208879425603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-17120765215805978931573604870000000000000)
      constant := (520509328206830067793558592045791120574397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree100.table
  base := (-7616312631490577329678427372240894590171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1248450)
      previous := (0)
      next := (812000)
      square := (5713402027000139315332516232730000000000000)
      linear := (-712284374795291607641856111146230000000000000)
      constant := (21868727224003162803244930478460324974833643261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree100.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel100

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486204650600469391831/100000000000000000000)
  centralHi := (60775581325058673979/12500000000000000000)
  directionLo := (244327029904182156067/50000000000000000000)
  directionHi := (97730811961672862427/20000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree101.table
  base := (-7588189663736320047226664881730647781533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-17287138639873541046121374034000000000000)
      constant := (530859822238639928197190628989469352218467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree101.table
  base := (-948523717548449014330410395917146123879/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-359604002418931602519380762453045000000000000)
      constant := (11151782433036039513145405598584381301524281156) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree101.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel101

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244327029904182156067/50000000000000000000)
  centralHi := (97730811961672862427/20000000000000000000)
  directionLo := (245545626141491497687/50000000000000000000)
  directionHi := (3928730018263863963/800000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree102.table
  base := (-7557689035151528236386577576956593482069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-17453512063941103160669143198000000000000)
      constant := (541312518078369113270067871463843406517931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree102.table
  base := (-7557689098561723808063734538172889856387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (1248450)
      previous := (0)
      next := (812000)
      square := (5713402027000139315332516232730000000000000)
      linear := (-726131634880434802435666938665950000000000000)
      constant := (22742695598758398117374467277266813381908148117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree102.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel102

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245545626141491497687/50000000000000000000)
  centralHi := (3928730018263863963/800000000000000000)
  directionLo := (246758204509262678299/50000000000000000000)
  directionHi := (493516409018525356599/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 3
  qDenominator := 5
  table := BinomialMassData.Q3_5.Degree103.table
  base := (-7524810679251365500383784666601297797729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (20)
      square := (138644520056301762123140970000000000000)
      linear := (-17619885488008665275216912362000000000000)
      constant := (551867415699854206536836481042198702202271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3_5.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree103.table
  base := (-940601341462848077443710198648999737319/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (624225)
      previous := (0)
      next := (406000)
      square := (2856701013500069657666258116365000000000000)
      linear := (-366527632461503199916286176212905000000000000)
      constant := (11593059710501734302575042172675223479299285316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree103.checked
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
end ForestUnimodality.Stage170KernelData.Cell291.Kernel103

namespace ForestUnimodality.Stage170KernelData.Cell291
open FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem degreePropagationThreshold : row.degreePropagationCheck 103 interval.lo interval.hi = true := by
  decide +kernel

theorem degreePropagationTail (n : ℕ) (hn : 103 ≤ n) (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual n j q :=
  row.degreePropagationCheck_sound 103 interval.lo interval.hi degreePropagationThreshold
    (fun _q hq j => Kernel103.actual_residual_nonneg j hq) n hn q hq j
end ForestUnimodality.Stage170KernelData.Cell291

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel104
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 104 j q :=
  degreePropagationTail 104 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel104

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel105
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 105 j q :=
  degreePropagationTail 105 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel105

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel106
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 106 j q :=
  degreePropagationTail 106 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel106

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel107
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 107 j q :=
  degreePropagationTail 107 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel107

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel108
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 108 j q :=
  degreePropagationTail 108 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel108

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel109
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 109 j q :=
  degreePropagationTail 109 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel109

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel110
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 110 j q :=
  degreePropagationTail 110 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel110

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel111
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 111 j q :=
  degreePropagationTail 111 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel111

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel112
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 112 j q :=
  degreePropagationTail 112 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel112

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel113
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 113 j q :=
  degreePropagationTail 113 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel113

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel114
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 114 j q :=
  degreePropagationTail 114 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel114

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel115
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 115 j q :=
  degreePropagationTail 115 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel115

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel116
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 116 j q :=
  degreePropagationTail 116 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel116

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel117
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 117 j q :=
  degreePropagationTail 117 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel117

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel118
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 118 j q :=
  degreePropagationTail 118 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel118

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel119
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 119 j q :=
  degreePropagationTail 119 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel119

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel120
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 120 j q :=
  degreePropagationTail 120 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel120

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel121
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 121 j q :=
  degreePropagationTail 121 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel121

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel122
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 122 j q :=
  degreePropagationTail 122 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel122

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel123
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 123 j q :=
  degreePropagationTail 123 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel123

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel124
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 124 j q :=
  degreePropagationTail 124 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel124

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel125
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 125 j q :=
  degreePropagationTail 125 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel125

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel126
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 126 j q :=
  degreePropagationTail 126 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel126

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel127
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 127 j q :=
  degreePropagationTail 127 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel127

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel128
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 128 j q :=
  degreePropagationTail 128 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel128

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel129
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 129 j q :=
  degreePropagationTail 129 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel129

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel130
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  degreePropagationTail 130 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel130

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel131
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  degreePropagationTail 131 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel131

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel132
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  degreePropagationTail 132 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel132

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel133
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  degreePropagationTail 133 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel133

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel134
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  degreePropagationTail 134 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel134

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel135
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  degreePropagationTail 135 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel135

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel136
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  degreePropagationTail 136 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel136

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel137
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  degreePropagationTail 137 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel137

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel138
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  degreePropagationTail 138 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel138

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel139
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  degreePropagationTail 139 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel139

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel140
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  degreePropagationTail 140 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel140

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel141
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  degreePropagationTail 141 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel141

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel142
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  degreePropagationTail 142 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel142

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel143
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  degreePropagationTail 143 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel143

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel144
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  degreePropagationTail 144 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel144

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel145
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  degreePropagationTail 145 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel145

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel146
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  degreePropagationTail 146 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel146

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel147
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  degreePropagationTail 147 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel147

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel148
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  degreePropagationTail 148 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel148

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel149
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  degreePropagationTail 149 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel149

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel150
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  degreePropagationTail 150 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel150

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel151
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  degreePropagationTail 151 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel151

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel152
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  degreePropagationTail 152 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel152

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel153
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  degreePropagationTail 153 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel153

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel154
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  degreePropagationTail 154 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel154

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel155
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  degreePropagationTail 155 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel155

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel156
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  degreePropagationTail 156 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel156

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel157
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  degreePropagationTail 157 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel157

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel158
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  degreePropagationTail 158 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel158

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel159
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  degreePropagationTail 159 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel159

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel160
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  degreePropagationTail 160 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel160

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel161
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  degreePropagationTail 161 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel161

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel162
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  degreePropagationTail 162 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel162

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel163
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  degreePropagationTail 163 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel163

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel164
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  degreePropagationTail 164 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel164

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel165
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  degreePropagationTail 165 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel165

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel166
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  degreePropagationTail 166 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel166

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel167
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  degreePropagationTail 167 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel167

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel168
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  degreePropagationTail 168 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel168

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel169
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  degreePropagationTail 169 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel169

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel170
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 170 j q :=
  degreePropagationTail 170 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel170

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel171
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 171 j q :=
  degreePropagationTail 171 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel171

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel172
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 172 j q :=
  degreePropagationTail 172 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel172

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel173
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 173 j q :=
  degreePropagationTail 173 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel173

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel174
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 174 j q :=
  degreePropagationTail 174 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel174

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel175
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 175 j q :=
  degreePropagationTail 175 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel175

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel176
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 176 j q :=
  degreePropagationTail 176 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel176

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel177
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 177 j q :=
  degreePropagationTail 177 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel177

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel178
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 178 j q :=
  degreePropagationTail 178 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel178

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel179
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 179 j q :=
  degreePropagationTail 179 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel179

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel180
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 180 j q :=
  degreePropagationTail 180 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel180

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel181
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 181 j q :=
  degreePropagationTail 181 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel181

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel182
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 182 j q :=
  degreePropagationTail 182 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel182

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel183
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 183 j q :=
  degreePropagationTail 183 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel183

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel184
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 184 j q :=
  degreePropagationTail 184 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel184

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel185
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 185 j q :=
  degreePropagationTail 185 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel185

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel186
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 186 j q :=
  degreePropagationTail 186 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel186

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel187
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 187 j q :=
  degreePropagationTail 187 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel187

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel188
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 188 j q :=
  degreePropagationTail 188 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel188

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel189
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 189 j q :=
  degreePropagationTail 189 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel189

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel190
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 190 j q :=
  degreePropagationTail 190 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel190

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel191
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 191 j q :=
  degreePropagationTail 191 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel191

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel192
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 192 j q :=
  degreePropagationTail 192 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel192

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel193
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 193 j q :=
  degreePropagationTail 193 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel193

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel194
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 194 j q :=
  degreePropagationTail 194 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel194

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel195
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 195 j q :=
  degreePropagationTail 195 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel195

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel196
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 196 j q :=
  degreePropagationTail 196 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel196

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel197
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 197 j q :=
  degreePropagationTail 197 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel197

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel198
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 198 j q :=
  degreePropagationTail 198 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel198

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel199
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 199 j q :=
  degreePropagationTail 199 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel199

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel200
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 200 j q :=
  degreePropagationTail 200 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel200

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel201
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 201 j q :=
  degreePropagationTail 201 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel201

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel202
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 202 j q :=
  degreePropagationTail 202 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel202

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel203
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 203 j q :=
  degreePropagationTail 203 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel203

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel204
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 204 j q :=
  degreePropagationTail 204 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel204

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel205
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 205 j q :=
  degreePropagationTail 205 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel205

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel206
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 206 j q :=
  degreePropagationTail 206 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel206

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel207
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 207 j q :=
  degreePropagationTail 207 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel207

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel208
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 208 j q :=
  degreePropagationTail 208 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel208

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel209
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 209 j q :=
  degreePropagationTail 209 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel209

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel210
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 210 j q :=
  degreePropagationTail 210 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel210

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel211
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 211 j q :=
  degreePropagationTail 211 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel211

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel212
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 212 j q :=
  degreePropagationTail 212 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel212

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel213
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 213 j q :=
  degreePropagationTail 213 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel213

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel214
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 214 j q :=
  degreePropagationTail 214 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel214

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel215
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 215 j q :=
  degreePropagationTail 215 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel215

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel216
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 216 j q :=
  degreePropagationTail 216 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel216

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel217
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 217 j q :=
  degreePropagationTail 217 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel217

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel218
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 218 j q :=
  degreePropagationTail 218 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel218

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel219
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 219 j q :=
  degreePropagationTail 219 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel219

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel220
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 220 j q :=
  degreePropagationTail 220 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel220

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel221
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 221 j q :=
  degreePropagationTail 221 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel221

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel222
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 222 j q :=
  degreePropagationTail 222 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel222

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel223
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 223 j q :=
  degreePropagationTail 223 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel223

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel224
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 224 j q :=
  degreePropagationTail 224 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel224

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel225
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 225 j q :=
  degreePropagationTail 225 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel225

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel226
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 226 j q :=
  degreePropagationTail 226 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel226

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel227
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 227 j q :=
  degreePropagationTail 227 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel227

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel228
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 228 j q :=
  degreePropagationTail 228 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel228

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel229
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 229 j q :=
  degreePropagationTail 229 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel229

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel230
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 230 j q :=
  degreePropagationTail 230 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel230

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel231
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 231 j q :=
  degreePropagationTail 231 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel231

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel232
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 232 j q :=
  degreePropagationTail 232 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel232

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel233
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 233 j q :=
  degreePropagationTail 233 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel233

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel234
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 234 j q :=
  degreePropagationTail 234 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel234

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel235
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 235 j q :=
  degreePropagationTail 235 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel235

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel236
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 236 j q :=
  degreePropagationTail 236 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel236

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel237
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 237 j q :=
  degreePropagationTail 237 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel237

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel238
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 238 j q :=
  degreePropagationTail 238 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel238

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel239
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 239 j q :=
  degreePropagationTail 239 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel239

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel240
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 240 j q :=
  degreePropagationTail 240 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel240

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel241
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 241 j q :=
  degreePropagationTail 241 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel241

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel242
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 242 j q :=
  degreePropagationTail 242 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel242

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel243
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 243 j q :=
  degreePropagationTail 243 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel243

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel244
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 244 j q :=
  degreePropagationTail 244 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel244

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel245
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 245 j q :=
  degreePropagationTail 245 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel245

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel246
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 246 j q :=
  degreePropagationTail 246 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel246

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel247
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 247 j q :=
  degreePropagationTail 247 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel247

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel248
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 248 j q :=
  degreePropagationTail 248 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel248

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel249
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 249 j q :=
  degreePropagationTail 249 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel249

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel250
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 250 j q :=
  degreePropagationTail 250 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel250

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel251
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 251 j q :=
  degreePropagationTail 251 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel251

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel252
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 252 j q :=
  degreePropagationTail 252 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel252

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel253
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 253 j q :=
  degreePropagationTail 253 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel253

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel254
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 254 j q :=
  degreePropagationTail 254 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel254

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel255
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 255 j q :=
  degreePropagationTail 255 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel255

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel256
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 256 j q :=
  degreePropagationTail 256 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel256

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel257
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 257 j q :=
  degreePropagationTail 257 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel257

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel258
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 258 j q :=
  degreePropagationTail 258 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel258

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel259
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 259 j q :=
  degreePropagationTail 259 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel259

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel260
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 260 j q :=
  degreePropagationTail 260 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel260

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel261
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 261 j q :=
  degreePropagationTail 261 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel261

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel262
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 262 j q :=
  degreePropagationTail 262 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel262

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel263
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 263 j q :=
  degreePropagationTail 263 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel263

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel264
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 264 j q :=
  degreePropagationTail 264 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel264

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel265
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 265 j q :=
  degreePropagationTail 265 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel265

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel266
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 266 j q :=
  degreePropagationTail 266 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel266

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel267
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 267 j q :=
  degreePropagationTail 267 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel267

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel268
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 268 j q :=
  degreePropagationTail 268 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel268

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel269
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 269 j q :=
  degreePropagationTail 269 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel269

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel270
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 270 j q :=
  degreePropagationTail 270 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel270

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel271
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 271 j q :=
  degreePropagationTail 271 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel271

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel272
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 272 j q :=
  degreePropagationTail 272 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel272

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel273
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 273 j q :=
  degreePropagationTail 273 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel273

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel274
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 274 j q :=
  degreePropagationTail 274 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel274

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel275
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 275 j q :=
  degreePropagationTail 275 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel275

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel276
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 276 j q :=
  degreePropagationTail 276 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel276

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel277
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 277 j q :=
  degreePropagationTail 277 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel277

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel278
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 278 j q :=
  degreePropagationTail 278 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel278

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel279
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 279 j q :=
  degreePropagationTail 279 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel279

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel280
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 280 j q :=
  degreePropagationTail 280 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel280

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel281
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 281 j q :=
  degreePropagationTail 281 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel281

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel282
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 282 j q :=
  degreePropagationTail 282 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel282

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel283
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 283 j q :=
  degreePropagationTail 283 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel283

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel284
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 284 j q :=
  degreePropagationTail 284 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel284

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel285
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 285 j q :=
  degreePropagationTail 285 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel285

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel286
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 286 j q :=
  degreePropagationTail 286 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel286

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel287
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 287 j q :=
  degreePropagationTail 287 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel287

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel288
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 288 j q :=
  degreePropagationTail 288 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel288

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel289
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 289 j q :=
  degreePropagationTail 289 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel289

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel290
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 290 j q :=
  degreePropagationTail 290 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel290

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel291
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 291 j q :=
  degreePropagationTail 291 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel291

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel292
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 292 j q :=
  degreePropagationTail 292 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel292

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel293
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 293 j q :=
  degreePropagationTail 293 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel293

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel294
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 294 j q :=
  degreePropagationTail 294 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel294

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel295
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 295 j q :=
  degreePropagationTail 295 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel295

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel296
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 296 j q :=
  degreePropagationTail 296 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel296

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel297
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 297 j q :=
  degreePropagationTail 297 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel297

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel298
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 298 j q :=
  degreePropagationTail 298 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel298

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel299
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 299 j q :=
  degreePropagationTail 299 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel299

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel300
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 300 j q :=
  degreePropagationTail 300 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel300

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel301
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 301 j q :=
  degreePropagationTail 301 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel301

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel302
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 302 j q :=
  degreePropagationTail 302 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel302

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel303
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 303 j q :=
  degreePropagationTail 303 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel303

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel304
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 304 j q :=
  degreePropagationTail 304 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel304

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel305
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 305 j q :=
  degreePropagationTail 305 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel305

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel306
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 306 j q :=
  degreePropagationTail 306 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel306

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel307
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 307 j q :=
  degreePropagationTail 307 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel307

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel308
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 308 j q :=
  degreePropagationTail 308 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel308

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel309
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 309 j q :=
  degreePropagationTail 309 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel309

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel310
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 310 j q :=
  degreePropagationTail 310 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel310

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel311
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 311 j q :=
  degreePropagationTail 311 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel311

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel312
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 312 j q :=
  degreePropagationTail 312 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel312

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel313
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 313 j q :=
  degreePropagationTail 313 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel313

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel314
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 314 j q :=
  degreePropagationTail 314 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel314

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel315
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 315 j q :=
  degreePropagationTail 315 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel315

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel316
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 316 j q :=
  degreePropagationTail 316 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel316

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel317
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 317 j q :=
  degreePropagationTail 317 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel317

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel318
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 318 j q :=
  degreePropagationTail 318 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel318

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel319
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 319 j q :=
  degreePropagationTail 319 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel319

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel320
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 320 j q :=
  degreePropagationTail 320 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel320

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel321
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 321 j q :=
  degreePropagationTail 321 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel321

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel322
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 322 j q :=
  degreePropagationTail 322 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel322

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel323
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 323 j q :=
  degreePropagationTail 323 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel323

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel324
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 324 j q :=
  degreePropagationTail 324 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel324

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel325
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 325 j q :=
  degreePropagationTail 325 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel325

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel326
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 326 j q :=
  degreePropagationTail 326 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel326

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel327
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 327 j q :=
  degreePropagationTail 327 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel327

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel328
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 328 j q :=
  degreePropagationTail 328 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel328

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel329
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 329 j q :=
  degreePropagationTail 329 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel329

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel330
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 330 j q :=
  degreePropagationTail 330 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel330

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel331
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 331 j q :=
  degreePropagationTail 331 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel331

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel332
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 332 j q :=
  degreePropagationTail 332 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel332

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel333
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 333 j q :=
  degreePropagationTail 333 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel333

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel334
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 334 j q :=
  degreePropagationTail 334 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel334

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel335
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 335 j q :=
  degreePropagationTail 335 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel335

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel336
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 336 j q :=
  degreePropagationTail 336 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel336

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel337
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 337 j q :=
  degreePropagationTail 337 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel337

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel338
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 338 j q :=
  degreePropagationTail 338 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel338

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel339
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 339 j q :=
  degreePropagationTail 339 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel339

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel340
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 340 j q :=
  degreePropagationTail 340 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel340

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel341
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 341 j q :=
  degreePropagationTail 341 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel341

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel342
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 342 j q :=
  degreePropagationTail 342 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel342

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel343
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 343 j q :=
  degreePropagationTail 343 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel343

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel344
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 344 j q :=
  degreePropagationTail 344 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel344

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel345
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 345 j q :=
  degreePropagationTail 345 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel345

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel346
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 346 j q :=
  degreePropagationTail 346 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel346

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel347
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 347 j q :=
  degreePropagationTail 347 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel347

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel348
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 348 j q :=
  degreePropagationTail 348 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel348

namespace ForestUnimodality.Stage170KernelData.Cell291.Kernel349
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 103 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 349 j q :=
  degreePropagationTail 349 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell291.Kernel349

