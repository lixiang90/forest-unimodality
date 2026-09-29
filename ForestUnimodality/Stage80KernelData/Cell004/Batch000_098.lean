import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell004.Parameters
import ForestUnimodality.BinomialMassData.Q39_140.Batch000_049
import ForestUnimodality.BinomialMassData.Q39_140.Batch050_099
import ForestUnimodality.BinomialMassData.Q2_7.Batch000_049
import ForestUnimodality.BinomialMassData.Q2_7.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel000
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
  base := (901590428059259672231462443/200000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (3269257360113995633521533062500000000000)
      constant := (394445812275926106601264818812500000000000) }

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
  base := (901590428059259672231462443/200000000000000000000000000)
  polynomial :=
    { denominator := 4375000000000000000000000000000000000000
      center := (5)
      previous := (2)
      next := (0)
      square := (114290268197998741515203359375000000000)
      linear := (163462868005699781676076653125000000000)
      constant := (19722290613796305330063240940625000000000) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel001
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
  base := (4035069229488234442162892867809550382653/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (1995737228764866799494981343750000000000)
      constant := (281721507532153997969660914811512276785710) }

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
  base := (31959959213022624322707497237333545918367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (1570466293138065155821081450000000000000)
      constant := (223121732750982761450004150961334821428569) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel002
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
  base := (22931065313233328201592644076808959183673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (2888868389662951861873718500000000000000)
      constant := (798139642996204783902582298550813571428555) }

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
  base := (5617243490894740510053062185557994897959/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17500000000000000000000000000000000000000
      center := (20)
      previous := (8)
      next := (0)
      square := (457161072791994966060813437500000000000)
      linear := (131381674546233451206234112500000000000)
      constant := (39096352108672031405254137948905964285713) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel003
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
  base := (2010070012922028618597736367172804914723/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (-551303033933390868558122093750000000000)
      constant := (139569184275387964882196120404440094030610) }

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
  base := (15581027094926907546861043813538601696793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-519412896768197546171208550000000000000)
      constant := (108168906953921353273464727594770211877551) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel004
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
  base := (5520273149139832865891562346688156370153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (202)
      previous := (78)
      next := (0)
      square := (4571610727919949660608134375000000000000)
      linear := (-3649646330565039405169347625000000000000)
      constant := (191600047831367648554589324684085472955355) }

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
  base := (211210698988474745030735644738549092531/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (40)
      previous := (16)
      next := (0)
      square := (914322145583989932121626875000000000000)
      linear := (-782176245860664448583676775000000000000)
      constant := (36661571352591689634764488429246091192925) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel005
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
  base := (3656163227436893986569261990589944075117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (202)
      previous := (78)
      next := (0)
      square := (4571610727919949660608134375000000000000)
      linear := (-6196686593263297073222451062500000000000)
      constant := (127727654086155163216370527037835542629095) }

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
  base := (3439949340226920702099987721825994312089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (40)
      previous := (16)
      next := (0)
      square := (914322145583989932121626875000000000000)
      linear := (-1304646043337230124081749275000000000000)
      constant := (24077461881082467679466439802781960184623) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel006
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
  base := (4554438567613306435224619404737146378409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-17487453711923109482551109000000000000000)
      constant := (163091204436191824182650266878300123244315) }

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
  base := (41804568493626083411535570331204644373/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17500000000000000000000000000000000000000
      center := (20)
      previous := (8)
      next := (0)
      square := (457161072791994966060813437500000000000)
      linear := (-913557920406897899789910887500000000000)
      constant := (7538405013570934973949242757960812765275) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel007
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
  base := (31167235676518514115173732838339517117/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (-5645383559329906204664328968750000000000)
      constant := (24133788017798472687485838995431411981900) }

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
  base := (2178925528409748580191136420990075652133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-4699171276580722950155788550000000000000)
      constant := (17336244087357766504676517046930529564931) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel008
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
  base := (467723702114422341368225915345495953889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (202)
      previous := (78)
      next := (0)
      square := (4571610727919949660608134375000000000000)
      linear := (-13837807381358070077381761375000000000000)
      constant := (24503827110692584050836738887092358386115) }

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
  base := (16911022759493223877425583283044576509/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8750000000000000000000000000000000000000
      center := (10)
      previous := (4)
      next := (0)
      square := (228580536395997483030406718750000000000)
      linear := (-718013858941731787643991693750000000000)
      constant := (1038843651359785377757710714906560177815) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel009
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
  base := (-64100828022510963700562761331112212249/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (-8192423822028163872717432406250000000000)
      constant := (3928011833968805741758020030754822571285) }

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
  base := (-466408088450503417835439086795598700503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-6789050466486985652148078550000000000000)
      constant := (2101257838783919262005879092430809096479) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel010
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
  base := (-73841815077628194473993434150913363101/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (-9465943953377292706743984125000000000000)
      constant := (-1706754927394069160084952515502870834140) }

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
  base := (-269928398315227261413096049150882352301/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-7833990061440117003144223550000000000000)
      constant := (-1992373693391639154705508720280882330535) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel011
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
  base := (-955839708916656128936197481153086069043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (202)
      previous := (78)
      next := (0)
      square := (4571610727919949660608134375000000000000)
      linear := (-21478928169452843081541071687500000000000)
      constant := (-10563542063092030839839610460670512416505) }

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
  base := (-2045007548929196590313221805716529470831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-8878929656393248354140368550000000000000)
      constant := (-4472372635172580372113329340015706295817) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel012
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
  base := (-99965379769827477771512404766233280417/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-48051936864302201499188350250000000000000)
      constant := (-29011647747313219922688218370454120364875) }

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
  base := (-325495598354220759399988243842453520337/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8750000000000000000000000000000000000000
      center := (10)
      previous := (4)
      next := (0)
      square := (228580536395997483030406718750000000000)
      linear := (-1240483656418297463142064193750000000000)
      constant := (-712369896353434630445784756897174642359) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel013
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
  base := (-1490784357682691776576877874389203716263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (202)
      previous := (78)
      next := (0)
      square := (4571610727919949660608134375000000000000)
      linear := (-26573008694849358417647278562500000000000)
      constant := (-15900708071990522375346669511434630069205) }

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
  base := (-3063420627963490306426268042704031316743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-10968808846299511056132658550000000000000)
      constant := (-5930481759071847981969502398928219217201) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel014
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
  base := (-3386310582907509239371764312321271783249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-58240097915095232171400764000000000000000)
      constant := (-30452886876216286585248219018744512413715) }

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
  base := (-3449843226180332616843673762107057930129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-12013748441252642407128803550000000000000)
      constant := (-5352217476939436517282562134749405510903) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel015
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
  base := (-1866575752325734344319839818287191155359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (202)
      previous := (78)
      next := (0)
      square := (4571610727919949660608134375000000000000)
      linear := (-31667089220245873753753485437500000000000)
      constant := (-12829379608149054712888696147864190437565) }

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
  base := (-945553426724648944082014334467753510801/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17500000000000000000000000000000000000000
      center := (20)
      previous := (8)
      next := (0)
      square := (457161072791994966060813437500000000000)
      linear := (-3264672009051443439531237137500000000000)
      constant := (-1024258550582590509659249216274274575607) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel016
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
  base := (-1009106010199065847641288461563132855743/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (-17107064741472065710903294437500000000000)
      constant := (-4480168192797891352137170804709649951005) }

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
  base := (-4074143558693149087216421316519216440093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-14103627631158905109121093550000000000000)
      constant := (-2260212355268709662391824415634515080651) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel017
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
  base := (-4306507285585614141791672589258169595017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-73522339491284778179719384625000000000000)
      constant := (-7601895839426882416084089464660935825595) }

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
  base := (-1083848346613747961896585818692293373403/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17500000000000000000000000000000000000000
      center := (20)
      previous := (8)
      next := (0)
      square := (457161072791994966060813437500000000000)
      linear := (-3787141806528009115029309637500000000000)
      constant := (22480957502131381227478044153946386179) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel018
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
  base := (-4550917221269587926090040473584067273961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-78616420016681293515825591500000000000000)
      constant := (5034512200243595119638227687057645411365) }

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
  base := (-2286481103912755484490487940453745669417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (40)
      previous := (16)
      next := (0)
      square := (914322145583989932121626875000000000000)
      linear := (-8096753410532583905556691775000000000000)
      constant := (1452190615005817571233072116823780314081) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel019
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
  base := (-4775096425243295405268436776117218811749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-83710500542077808851931798375000000000000)
      constant := (19798061138990994035331993545272341588785) }

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
  base := (-958373738270855820586404549850111834647/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-17238446416018299162109528550000000000000)
      constant := (6148029164893610629554946455246085787355) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel020
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
  base := (-311436625270759983994862794070815439477/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (-22201145266868581047009501312500000000000)
      constant := (9137703059481375892578548955085838473220) }

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
  base := (-4995711433201021494041081389896778655921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-18283386010971430513105673550000000000000)
      constant := (9795677461536375273965136270722549408553) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel021
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
  base := (-103548795896825668806714571927760134683/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (202)
      previous := (78)
      next := (0)
      square := (4571610727919949660608134375000000000000)
      linear := (-46949330796435419762072106062500000000000)
      constant := (27596440613184268142084691380397382152375) }

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
  base := (-5187070752937151041997927460482952802943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-19328325605924561864101818550000000000000)
      constant := (13829263882940038777868284076619330379399) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel022
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
  base := (-5360524320051313159544835331381366806527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-98992742118267354860250419000000000000000)
      constant := (75651939789497458901105613514152161771555) }

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
  base := (-2683898413316180111044872086965018366851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (40)
      previous := (16)
      next := (0)
      square := (914322145583989932121626875000000000000)
      linear := (-10186632600438846607548981775000000000000)
      constant := (9117918598308376907127053691244871432043) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel023
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
  base := (-138343400207369369030681618966654944779/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (-26021705660915967549089156468750000000000)
      constant := (24468903233918466583061998345264519327350) }

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
  base := (-5539216304067631420687731867192450945261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-21418204795830824566094108550000000000000)
      constant := (23006110854099643678524203829652843383173) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel024
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
  base := (-1424539622420718748924920799465587614659/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (-27295225792265096383115708187500000000000)
      constant := (30456493402751380579128300293704433486935) }

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
  base := (-5702280467017493732023278606970125923231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-22463144390783955917090253550000000000000)
      constant := (28133425882967004711058856951209118537383) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel025
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
  base := (-5854576498146869997265854284760184137449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-114274983694456900868569039625000000000000)
      constant := (147475556127898462153269509642768555189285) }

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
  base := (-2928835732623767203414371268582618856677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (40)
      previous := (16)
      next := (0)
      square := (914322145583989932121626875000000000000)
      linear := (-11754041992868543634043199275000000000000)
      constant := (16806503617429863078365779869921668003261) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel026
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
  base := (-6003558348265299774190800249148338022569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-119369064219853416204675246500000000000000)
      constant := (174804469476103785553241140742308169210085) }

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
  base := (-1201175698004749218141650430187205320577/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-24553023580690218619082543550000000000000)
      constant := (39441430570915859496313412743447813779805) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel027
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
  base := (-192047364234169722732589124238325619877/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (-31115786186312482885195363343750000000000)
      constant := (50949576778671788620634128378112576434440) }

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
  base := (-6147252390485359316986503516929679909949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-25597963175643349970078688550000000000000)
      constant := (45616239947160790996531543481492240630357) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel028
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
  base := (-98136665275655210119104820199020273059/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (-32389306317661611719221915062500000000000)
      constant := (58611658380068785067532790488548647086960) }

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
  base := (-3141022416183337227881220461194863100883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (40)
      previous := (16)
      next := (0)
      square := (914322145583989932121626875000000000000)
      linear := (-13321451385298240660537416775000000000000)
      constant := (26067836851727209033346670971635958293819) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel029
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
  base := (-6409467123909823310322727400741924969669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-134651305796042962212993867125000000000000)
      constant := (266741888370902162770292570058407626061585) }

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
  base := (-6410436373084276155787732996045805278943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-27687842365549612672070978550000000000000)
      constant := (58998467937880648165537127727679363047399) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel030
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
  base := (-6531833823729656050336177373738642049703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-139745386321439477549100074000000000000000)
      constant := (300678593136428785265256334231647528260395) }

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
  base := (-816569573719108995311402433056799913821/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8750000000000000000000000000000000000000
      center := (10)
      previous := (4)
      next := (0)
      square := (228580536395997483030406718750000000000)
      linear := (-3591597745062843002883390443750000000000)
      constant := (8275464451329566059382627843602400603253) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel031
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
  base := (-3323980069741961160361551637888141060283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (202)
      previous := (78)
      next := (0)
      square := (4571610727919949660608134375000000000000)
      linear := (-72419733423417996442603140437500000000000)
      constant := (168126388316733917448960442116102562890095) }

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
  base := (-1329699701851541269636017201994699132769/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-29777721555455875374063268550000000000000)
      constant := (73750765533525347689114727230185530353085) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel032
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
  base := (-675792834944033856515760766821572419821/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (202)
      previous := (78)
      next := (0)
      square := (4571610727919949660608134375000000000000)
      linear := (-74966773686116254110656243875000000000000)
      constant := (186730779561324618069846315206224826531325) }

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
  base := (-844791119138735173758239892110598623031/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8750000000000000000000000000000000000000
      center := (10)
      previous := (4)
      next := (0)
      square := (228580536395997483030406718750000000000)
      linear := (-3852832643801125840632426693750000000000)
      constant := (10204893744496173908402141955225809638783) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel033
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
  base := (-3430899075478780110532118039723841265873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (202)
      previous := (78)
      next := (0)
      square := (4571610727919949660608134375000000000000)
      linear := (-77513813948814511778709347312500000000000)
      constant := (206151425598210024340356239639353055694445) }

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
  base := (-857761994180701690196491567603081689789/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8750000000000000000000000000000000000000
      center := (10)
      previous := (4)
      next := (0)
      square := (228580536395997483030406718750000000000)
      linear := (-3983450093170267259506944818750000000000)
      constant := (11233566581626893021925719014278428171477) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel034
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
  base := (-6959612889102060862925844187597802504363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-160121708423025538893524901500000000000000)
      constant := (452775135777453697414080482096576912347295) }

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
  base := (-6959834069279667081842700217751744652117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-32912540340315269427051703550000000000000)
      constant := (98438671711559256039668558675737787435181) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel035
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
  base := (-1762851016513979396756787335246216220397/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (-41303947237105513557407777093750000000000)
      constant := (123719327572344370992457882918726182286105) }

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
  base := (-3525784098732586455366370803295448889039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (40)
      previous := (16)
      next := (0)
      square := (914322145583989932121626875000000000000)
      linear := (-16978739967634200389023924275000000000000)
      constant := (53674696426814905490511959626931857776727) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel036
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
  base := (-3568597302920055384562426056967462256783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (202)
      previous := (78)
      next := (0)
      square := (4571610727919949660608134375000000000000)
      linear := (-85154934736909284782868657625000000000000)
      constant := (269304286195728547598240553956138821012595) }

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
  base := (-3568658152276848139574283443596034966777/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (40)
      previous := (16)
      next := (0)
      square := (914322145583989932121626875000000000000)
      linear := (-17501209765110766064521996775000000000000)
      constant := (58300285156682926051563131294827755232561) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel037
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
  base := (-3608500608960951735498898704797230553879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (202)
      previous := (78)
      next := (0)
      square := (4571610727919949660608134375000000000000)
      linear := (-87701974999607542450921761062500000000000)
      constant := (291984168626169161965884819599284430614235) }

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
  base := (-7217091385105890477299672541863584913587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-36047359125174663480040138550000000000000)
      constant := (126192113128842806374509113306954905604891) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel038
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
  base := (-1458167221690584267925745919687229199891/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-180498030524611600237949729000000000000000)
      constant := (630956177656714272531301072567234890019075) }

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
  base := (-911362858187851593857652346164745895251/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8750000000000000000000000000000000000000
      center := (10)
      previous := (4)
      next := (0)
      square := (228580536395997483030406718750000000000)
      linear := (-4636537340015974353879535443750000000000)
      constant := (17015494414424159134430793751846778733243) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel039
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
  base := (-7358708219228180142696532476331495576957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-185592111050008115574055935875000000000000)
      constant := (679571780641759389126314475162772654806505) }

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
  base := (-3679378805145082527170773068700773913031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (40)
      previous := (16)
      next := (0)
      square := (914322145583989932121626875000000000000)
      linear := (-19068619157540463091016214275000000000000)
      constant := (73198024410598669262189794369094582608783) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel040
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
  base := (-7420624124746553106112064614769554298467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-190686191575404630910162142750000000000000)
      constant := (729814916100013110809929796983065599553655) }

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
  base := (-18551651609061273904356497047005588573/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4375000000000000000000000000000000000000
      center := (5)
      previous := (2)
      next := (0)
      square := (114290268197998741515203359375000000000)
      linear := (-2448886119377128595814285846875000000000)
      constant := (9813022404822441718955951266774021999725) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel041
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
  base := (-3738294340881197674244376743684431471463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (202)
      previous := (78)
      next := (0)
      square := (4571610727919949660608134375000000000000)
      linear := (-97890136050400573123134174812500000000000)
      constant := (390842707022536504215338538225732398498795) }

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
  base := (-7476615666514039316151534145573865226559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-40227117504987188884024718550000000000000)
      constant := (167960858376221108710583143280982943414087) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel042
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
  base := (-7526605499660729267227012672387916359997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-200874352626197661582374556500000000000000)
      constant := (835183148148463298079541838328922927400105) }

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
  base := (-1881656356923620813837385987265603249611/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17500000000000000000000000000000000000000
      center := (20)
      previous := (8)
      next := (0)
      square := (457161072791994966060813437500000000000)
      linear := (-10318014274985080058755215887500000000000)
      constant := (44813382319308339895443753739140777252723) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel043
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
  base := (-7570677281123386522232265091144743858517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-205968433151594176918480763375000000000000)
      constant := (890308023816319871659834280369308964951905) }

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
  base := (-7570691989598889815904148624762389496667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-42316996694893451586017008550000000000000)
      constant := (190886356743164481060898192526663273523331) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel044
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
  base := (-7608806068895935011216267743789611163179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-211062513676990692254586970250000000000000)
      constant := (947059969552547852751642907567363609288735) }

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
  base := (-1902204229784219527496544881893310030109/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17500000000000000000000000000000000000000
      center := (20)
      previous := (8)
      next := (0)
      square := (457161072791994966060813437500000000000)
      linear := (-10840484072461645734253288387500000000000)
      constant := (50714832451411784840689214126746829789237) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel045
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
  base := (-955124178072236890682969941776656962001/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (-54039148550596801897673294281250000000000)
      constant := (251359732675291006915000464571727762659930) }

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
  base := (-1528200284916259909786546659730600954081/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-44406875884799714288009298550000000000000)
      constant := (215172440006771374607991330409428966607165) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel046
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
  base := (-7667240558201051380946094066665231590159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-221250674727783722926799384000000000000000)
      constant := (1065444864911055938325913756379216894344435) }

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
  base := (-7667246453826606648237458460114018954829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-45451815479752845639005443550000000000000)
      constant := (227825680711276019188146074579201867316197) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel047
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
  base := (-1921887105544785895241299275983520534783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (-56586188813295059565726397718750000000000)
      constant := (281769434711935672908452800036670531282595) }

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
  base := (-3843776382479282405655845649822119589861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (40)
      previous := (16)
      next := (0)
      square := (914322145583989932121626875000000000000)
      linear := (-23248377537352988495000794275000000000000)
      constant := (120409523306280357639670867501245162870973) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel048
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
  base := (-7701917779461361579556565536364825522241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-231438835778576753599011797750000000000000)
      constant := (1190337525808002642692451798427231106721565) }

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
  base := (-1925480244243833029271019659165331359899/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17500000000000000000000000000000000000000
      center := (20)
      previous := (8)
      next := (0)
      square := (457161072791994966060813437500000000000)
      linear := (-11885423667414777085249433387500000000000)
      constant := (63538133344409589082269445985842680480707) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel049
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
  base := (-7710349253006915080020519566098232344903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-236532916303973268935118004625000000000000)
      constant := (1255224203988263451886324344145936867928395) }

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
  base := (-3855175803139219325866732347394264060251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (40)
      previous := (16)
      next := (0)
      square := (914322145583989932121626875000000000000)
      linear := (-24293317132306119845996939275000000000000)
      constant := (133913068695849115867051155918240151578243) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel050
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
  base := (-7712843361732563725798883200818303177491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-241626996829369784271224211500000000000000)
      constant := (1321737755226438531694964997033859388787815) }

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
  base := (-964105636620014215379977150787085297221/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8750000000000000000000000000000000000000
      center := (10)
      previous := (4)
      next := (0)
      square := (228580536395997483030406718750000000000)
      linear := (-6203946732445671380373752943750000000000)
      constant := (35229981946761842042494443069490402919453) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel051
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
  base := (-120459383541599397851070668923651726613/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (-61680269338691574901832604593750000000000)
      constant := (347469541021671498505795858530098783096720) }

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
  base := (-7709401819772451592493154920947252693593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-50676513454518502393986168550000000000000)
      constant := (296193685245563210316207350853369231144849) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel052
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
  base := (-962502648747390918304350458402779999047/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (-62953789470040703735859156312500000000000)
      constant := (364911354298151792974197967736805400066710) }

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
  base := (-3850011062923138119328624759146630178447/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (40)
      previous := (16)
      next := (0)
      square := (914322145583989932121626875000000000000)
      linear := (-25860726524735816872491156775000000000000)
      constant := (155443812016093942906455664485973588750871) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel053
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
  base := (-480294101808238177714655700045384394391/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (-64227309601389832569885708031250000000000)
      constant := (382759875685122208503750879352239934785260) }

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
  base := (-7684706316641658795015430222094429621721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-52766392644424765095978458550000000000000)
      constant := (325921669795748264895684174345338992647953) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel054
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
  base := (-766345416601343498314075112587737453577/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (202)
      previous := (78)
      next := (0)
      square := (4571610727919949660608134375000000000000)
      linear := (-131001659465477922807824519500000000000000)
      constant := (802030205071537587169628786753395945624025) }

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
  base := (-7663454671192199260294634999301945951011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-53811332239377896446974603550000000000000)
      constant := (341295820583009147573437321204886378342923) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel055
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
  base := (-190906676910845561867214150799273533661/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (-66774349864088090237938811468750000000000)
      constant := (419677032442005599512457412153848013218650) }

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
  base := (-1909066861851086857365509549497385864017/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17500000000000000000000000000000000000000
      center := (20)
      previous := (8)
      next := (0)
      square := (457161072791994966060813437500000000000)
      linear := (-13714067958582756949492687137500000000000)
      constant := (89252518647156346320350137278518298951881) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel056
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
  base := (-7603144613628683771261766850998409932411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-272191479981748876287861452750000000000000)
      constant := (1754982652745080639285285660115055652365615) }

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
  base := (-380157244297873962331547452923141885041/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17500000000000000000000000000000000000000
      center := (20)
      previous := (8)
      next := (0)
      square := (457161072791994966060813437500000000000)
      linear := (-13975302857321039787241723387500000000000)
      constant := (93266107531960336602695173347690034023565) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel057
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
  base := (-7564087013342082500496466716154242791753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-277285560507145391623967659625000000000000)
      constant := (1832883970823207671078361648343976502288645) }

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
  base := (-7564087213195992517330680575428064521219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-56946151024237290499963038550000000000000)
      constant := (389458885616246246322872563072003548351467) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel058
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
  base := (-234971703020975936255253370439780019681/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (-70594910258135476740018466625000000000000)
      constant := (478103019066000274501729283842486594489320) }

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
  base := (-3759547321647009020071539414223043265763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (40)
      previous := (16)
      next := (0)
      square := (914322145583989932121626875000000000000)
      linear := (-28995545309595210925479591775000000000000)
      constant := (203096719777310584713801617800438697139659) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel059
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
  base := (-1867041818088847285208333929338785503273/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (-71868430389484605574045018343750000000000)
      constant := (498391740440396678850367382587986257385445) }

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
  base := (-3734083689947022838192588580926842510893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (40)
      previous := (16)
      next := (0)
      square := (914322145583989932121626875000000000000)
      linear := (-29518015107071776600977664275000000000000)
      constant := (211634045258734343347876738783512102423749) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel060
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
  base := (-3705652769256546719809845107150403796911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (202)
      previous := (78)
      next := (0)
      square := (4571610727919949660608134375000000000000)
      linear := (-146283901041667468816143140125000000000000)
      constant := (1038174310190907927181277468249735867108115) }

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
  base := (-3705652808681972438866558277557157345627/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (40)
      previous := (16)
      next := (0)
      square := (914322145583989932121626875000000000000)
      linear := (-30040484904548342276475736775000000000000)
      constant := (220341418572106855982795151057099898580611) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel061
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
  base := (-1469701896795145940935310474509989677951/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-297661882608731452968392487125000000000000)
      constant := (2160757045515589975204945017845126806358575) }

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
  base := (-7348509541776142320449572846855675590331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-61125909404049815903947618550000000000000)
      constant := (458437678132349258503274978372010270867683) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel062
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
  base := (-3639889644662440965425740749918317853249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (202)
      previous := (78)
      next := (0)
      square := (4571610727919949660608134375000000000000)
      linear := (-151377981567063984152249347000000000000000)
      constant := (1123396115421276819054487599309108875136285) }

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
  base := (-181994483292088475288125219158205683221/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8750000000000000000000000000000000000000
      center := (10)
      previous := (4)
      next := (0)
      square := (228580536395997483030406718750000000000)
      linear := (-7771356124875368406867970443750000000000)
      constant := (59566576529000627407484283404462801087265) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel063
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
  base := (-1801278781927849508046695455428994047029/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (-76962510914881120910151225218750000000000)
      constant := (583613542575606791520791207731078958353985) }

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
  base := (-288204606349833351242384750802119960029/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-63215788593956078605939908550000000000000)
      constant := (494967638241563102424686807509629006994925) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel064
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
  base := (-712451716551282809653852264870137041879/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (202)
      previous := (78)
      next := (0)
      square := (4571610727919949660608134375000000000000)
      linear := (-156472062092460499488355553875000000000000)
      constant := (1211871429035998153026275744447726017671175) }

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
  base := (-7124517188244925480701496065329524307623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-64260728188909209956936053550000000000000)
      constant := (513742755004050216036175946742693329846639) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel065
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
  base := (-3518992781435222607491136986887826617037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (202)
      previous := (78)
      next := (0)
      square := (4571610727919949660608134375000000000000)
      linear := (-159019102355158757156408657312500000000000)
      constant := (1257329144273158249914745111388613568403705) }

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
  base := (-7037985579517313262277249290578178420689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-65305667783862341307932198550000000000000)
      constant := (532857961404110866031555424465952751055177) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel066
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
  base := (-55564163793087008071818680912589573689/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-323132285235714029648923521500000000000000)
      constant := (2607200456323080815662905556469920615110625) }

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
  base := (-3472760243161850048809354512745618619567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (40)
      previous := (16)
      next := (0)
      square := (914322145583989932121626875000000000000)
      linear := (-33175303689407736329464171775000000000000)
      constant := (276156628182710065804001213310780669663031) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel067
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
  base := (-3423561024124631276796673567070343138557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (202)
      previous := (78)
      next := (0)
      square := (4571610727919949660608134375000000000000)
      linear := (-164113182880555272492514864187500000000000)
      constant := (1350684678094692140462680026357225490150505) }

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
  base := (-6847122057170467537599579178318406907829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-67395546973768604009924488550000000000000)
      constant := (572108638848433341909401025851771151645197) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel068
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
  base := (-842848803633125043491385338284758987813/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (-83330111571626765080283983812500000000000)
      constant := (699291245777580763287081666995066870853090) }

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
  base := (-1348558087118742474613692350837586026041/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-68440486568721735360920633550000000000000)
      constant := (592244107848397819399811008120684489088565) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel069
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
  base := (-1326505151127366615477242672665508573109/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-338414526811903575657242142125000000000000)
      constant := (2894587332219016103342956898617910999705925) }

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
  base := (-6632525760413676251629861173949005096911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-69485426163674866711916778550000000000000)
      constant := (612719662393571872546000842482356964321623) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel070
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
  base := (-65163281624709889218309730709084480021/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (-85877151834325022748337087250000000000000)
      constant := (748409099701936361303430638957676079981625) }

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
  base := (-3258164082982670382102431411151101453409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (40)
      previous := (16)
      next := (0)
      square := (914322145583989932121626875000000000000)
      linear := (-35265182879313999031456461775000000000000)
      constant := (316767650771805315105761465621942289826137) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel071
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
  base := (-6394197779753792893439909700638190303191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-348602687862696606329454555875000000000000)
      constant := (3094312178319989703334514464112038339388315) }

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
  base := (-799274722788684529809687942670499825687/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8750000000000000000000000000000000000000
      center := (10)
      previous := (4)
      next := (0)
      square := (228580536395997483030406718750000000000)
      linear := (-8946913169197641176738633568750000000000)
      constant := (81836378048511087512823627063806501220191) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel072
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
  base := (-1253226946711710394084141124760463080249/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-353696768388093121665560762750000000000000)
      constant := (3196614666343183133468063740466918960956425) }

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
  base := (-6266134735427360013490647710265055907481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-72620244948534260764905213550000000000000)
      constant := (676186830045137140845899047628144608647633) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel073
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
  base := (-1226427829207063176673925489018255371201/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-358790848913489637001666969625000000000000)
      constant := (3300543858602073995043501053731180310039825) }

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
  base := (-6132139147401602963597902817586218217581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-73665184543487392115901358550000000000000)
      constant := (698022717660177676320977772176896472476933) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel074
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
  base := (-5992211135586244181027407998582798365081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-363884929438886152337773176500000000000000)
      constant := (3406099750952586703854900754712102057222165) }

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
  base := (-1498052784146239535831036041129134304697/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17500000000000000000000000000000000000000
      center := (20)
      previous := (8)
      next := (0)
      square := (457161072791994966060813437500000000000)
      linear := (-18677531034610130866724375887500000000000)
      constant := (180049671601185258786537765762096059867121) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel075
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
  base := (-1461587704257167813812795615463754437649/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (-92244752491070666918469845843750000000000)
      constant := (878320584844028639046815778048612344682285) }

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
  base := (-5846350817758572929638935155303720176803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-75755063733393654817893648550000000000000)
      constant := (742714735475359185682631976412873958762379) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel076
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
  base := (-2847279150873745676160334142840300221111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (202)
      previous := (78)
      next := (0)
      square := (4571610727919949660608134375000000000000)
      linear := (-187036545244839591504992795125000000000000)
      constant := (1811045809987093126710399007700589492261115) }

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
  base := (-5694558302280843165345011746047647677483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-76800003328346786168889793550000000000000)
      constant := (765570864092523357030801360577666466257619) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel077
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
  base := (-138420842445953472801221339463405351863/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (-94791792753768924586522949281250000000000)
      constant := (933131897240865397540512720133901876847950) }

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
  base := (-5536833698227803899809140471614449031129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-77844942923299917519885938550000000000000)
      constant := (788767071499701303845091849798698856782097) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel078
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
  base := (-1074635422048236462048817628545690568833/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-384261251540472213682198004000000000000000)
      constant := (3844590242671020673257729464517004150454225) }

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
  base := (-53731771105258244048786762694404858329/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17500000000000000000000000000000000000000
      center := (20)
      previous := (8)
      next := (0)
      square := (457161072791994966060813437500000000000)
      linear := (-19722470629563262217720520887500000000000)
      constant := (203075839240602110305642989878479149792425) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel079
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
  base := (-1040717728173871386838072292952536057301/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-389355332065868729018304210875000000000000)
      constant := (3958279577529917764152894135317681189972325) }

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
  base := (-5203588641077249454319889032534876920669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-79934822113206180221878228550000000000000)
      constant := (836179719767328355746877800472255861555317) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel080
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
  base := (-5028068388727718887562627584593481245529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-394449412591265244354410417750000000000000)
      constant := (4073595590074975899218921501539228156406485) }

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
  base := (-1257017097219883271468222484583382843913/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17500000000000000000000000000000000000000
      center := (20)
      previous := (8)
      next := (0)
      square := (457161072791994966060813437500000000000)
      linear := (-20244940427039827893218593387500000000000)
      constant := (215099039805369717288457148607916320092609) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel081
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
  base := (-484661645002749073606453268633823185239/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (202)
      previous := (78)
      next := (0)
      square := (4571610727919949660608134375000000000000)
      linear := (-199771746558330879845258312312500000000000)
      constant := (2095269138469401144328091973368768442583175) }

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
  base := (-4846616450138337095255565570056996613899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-82024701303112442923870518550000000000000)
      constant := (884952674651420348873399135309601023702707) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel082
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
  base := (-931846583658817261784766577763252952977/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-404637573642058275026622831500000000000000)
      constant := (4309107634848007448441710006753930733229025) }

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
  base := (-4659232918375008503906882510254871194941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-83069640898065574274866663550000000000000)
      constant := (909849265402503365755516657028215901635413) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel083
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
  base := (-4465917884469735942341243439483771623221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-409731654167454790362729038375000000000000)
      constant := (4429303660619613316808474647927442993187265) }

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
  base := (-1116479471132200998860909172342331179687/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17500000000000000000000000000000000000000
      center := (20)
      previous := (8)
      next := (0)
      square := (457161072791994966060813437500000000000)
      linear := (-21028645123254676406465702137500000000000)
      constant := (233771482709538280753715897018603681742191) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel084
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
  base := (-1066667859252770451014503365949161958123/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (-103706433673212826424708811312500000000000)
      constant := (1137781587789409354471383537716779331465695) }

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
  base := (-2133335718527095900128537294985153292873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (40)
      previous := (16)
      next := (0)
      square := (914322145583989932121626875000000000000)
      linear := (-42579760043985918488429476775000000000000)
      constant := (480331335169594171519350601535103926949889) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel085
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
  base := (-406149366198207151889538472531638256089/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (202)
      previous := (78)
      next := (0)
      square := (4571610727919949660608134375000000000000)
      linear := (-209959907609123910517470726062500000000000)
      constant := (2337287851724920792402072526924150805184425) }

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
  base := (-253843353875845658401160558182559569009/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4375000000000000000000000000000000000000
      center := (5)
      previous := (2)
      next := (0)
      square := (114290268197998741515203359375000000000)
      linear := (-5387778730182810520490943659375000000000)
      constant := (61661217706448282219658118311472083016937) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel086
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
  base := (-962596160785611158084468942478095083269/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (-106253473935911084092761914750000000000000)
      constant := (1199912928641158733368087301941391672085585) }

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
  base := (-770076928633079696298913295181911327693/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-87249399277878099678851243550000000000000)
      constant := (1012836369143795592457384530468633103530745) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel087
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
  base := (-3633344462032078610493209326377592377817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-430107976269040851707153865875000000000000)
      constant := (4926354381648121752576376317111159266776405) }

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
  base := (-227084028878051536882748043165106504583/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4375000000000000000000000000000000000000
      center := (5)
      previous := (2)
      next := (0)
      square := (114290268197998741515203359375000000000)
      linear := (-5518396179551951939365461784375000000000)
      constant := (64964582955642773201674550329094254467919) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel088
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
  base := (-1705186599025718846920634881319216999287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (202)
      previous := (78)
      next := (0)
      square := (4571610727919949660608134375000000000000)
      linear := (-217601028397218683521630036375000000000000)
      constant := (2527341850960642896849715214503827405024955) }

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
  base := (-1705186599031826601493355408862633372313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (40)
      previous := (16)
      next := (0)
      square := (914322145583989932121626875000000000000)
      linear := (-44669639233892181190421766775000000000000)
      constant := (533185178593419970711997585337961566393809) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel089
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
  base := (-3181470928538347980396627201600709656587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-440296137319833882379366279625000000000000)
      constant := (5184639672677303143411001589153350162019455) }

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
  base := (-3181470928547257614337342650569339931123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-90384218062737493731839678550000000000000)
      constant := (1093647458292100689989209778146014620482139) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel090
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
  base := (-589327545768260971891019447414644501717/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-445390217845230397715472486500000000000000)
      constant := (5316222291278976463085736251764937212199525) }

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
  base := (-2946637728847802514821987364505757591889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-91429157657690625082835823550000000000000)
      constant := (1121264630078629464087913765448459696856777) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel091
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
  base := (-676468418097375948074464993906739125973/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (-112621074592656728262894673343750000000000)
      constant := (1362357888789070977894698278278107880590945) }

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
  base := (-10823494689576967525327940441529103873/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (40)
      previous := (16)
      next := (0)
      square := (914322145583989932121626875000000000000)
      linear := (-46237048626321878216915984275000000000000)
      constant := (574610936016211792940933875763662034111125) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel092
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
  base := (-3842466923062143788605047392644243469/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (-113894594724005857096921225062500000000000)
      constant := (1396066865451009133821947787801192236573600) }

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
  base := (-61479470769080666193435218657144631419/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8750000000000000000000000000000000000000
      center := (10)
      previous := (4)
      next := (0)
      square := (228580536395997483030406718750000000000)
      linear := (-11689879605949610973103514193750000000000)
      constant := (147189897956555812354247653296999937900335) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel093
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
  base := (-2206553273740566804788628327290560978599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-460672459421419943723791107125000000000000)
      constant := (5720730008779638330529040665229205365749035) }

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
  base := (-2206553273743085352274367899247968472491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-94563976442550019135824258550000000000000)
      constant := (1206156564450179903176601422605264220692563) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel094
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
  base := (-121749816837074676915857031894495150897/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (-116441634986704114764974328500000000000000)
      constant := (1464704798425235890717158401512895678874420) }

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
  base := (-1947997069395030746419326973889609882861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-95608916037503150486820403550000000000000)
      constant := (1235134013949195309649393089382772730819973) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel095
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
  base := (-1683510284110397783702065798562969081469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-470860620472212974396003520875000000000000)
      constant := (5998535014244206273457584571534671082148585) }

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
  base := (-67340411364469437933303698862092964073/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-96653855632456281837816548550000000000000)
      constant := (1264451531684744006425234081199133731287225) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel096
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
  base := (-88318311417027485813368255962155600651/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (-118988675249402372433027431937500000000000)
      constant := (1534969367035529304619521606265298215908860) }

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
  base := (-1413092982673415035583473805677859151329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-97698795227409413188812693550000000000000)
      constant := (1294109117203364494961139232160254985940697) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel097
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
  base := (-1136745228300824213433185167781744252471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (404)
      previous := (156)
      next := (0)
      square := (9143221455839899321216268750000000000000)
      linear := (-481048781523006005068215934625000000000000)
      constant := (6282846553181923778410599384787013951163515) }

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
  base := (-45469809132061396763765283216050449117/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (80)
      previous := (32)
      next := (0)
      square := (1828644291167979864243253750000000000000)
      linear := (-98743734822362544539808838550000000000000)
      constant := (1324106770062506506880653414537191171404525) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell004.Kernel098
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
  base := (-53404192669359999713953650850052809911/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87500000000000000000000000000000000000000
      center := (101)
      previous := (39)
      next := (0)
      square := (2285805363959974830304067187500000000000)
      linear := (-121535715512100630101080535375000000000000)
      constant := (1606860566800907160522226870446617606612460) }

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
  base := (-427233541355138929380082929587248758787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (40)
      previous := (16)
      next := (0)
      square := (914322145583989932121626875000000000000)
      linear := (-49894337208657837945402491775000000000000)
      constant := (677222244915085383182253719192889258688491) }

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
end ForestUnimodality.Stage80KernelData.Cell004.Kernel098
