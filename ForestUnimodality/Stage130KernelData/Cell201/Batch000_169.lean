import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell201.Parameters
import ForestUnimodality.BinomialMassData.Q12116_22791.Batch000_049
import ForestUnimodality.BinomialMassData.Q12116_22791.Batch050_099
import ForestUnimodality.BinomialMassData.Q12116_22791.Batch100_149
import ForestUnimodality.BinomialMassData.Q12116_22791.Batch150_199
import ForestUnimodality.BinomialMassData.Q24257_45582.Batch000_049
import ForestUnimodality.BinomialMassData.Q24257_45582.Batch050_099
import ForestUnimodality.BinomialMassData.Q24257_45582.Batch100_149
import ForestUnimodality.BinomialMassData.Q24257_45582.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree000.table
  base := (769366184240868244314981443/10000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (154)
      previous := (77)
      next := (77)
      square := (685872305890301570130418440000000000000)
      linear := (-51956543106428648010064464000000000000)
      constant := (769366184240868244314981443000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree000.table
  base := (769366184240868244314981443/10000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (154)
      previous := (77)
      next := (77)
      square := (685872305890301570130418440000000000000)
      linear := (-51956543106428648010064464000000000000)
      constant := (769366184240868244314981443000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree001.table
  base := (104395171098415372944513948388809453126197/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-135258502008199445319009766125479088000000000000)
      constant := (72339611018438885815001970569393965417499947270876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree001.table
  base := (104304717467104390653367951591430553560579/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-135388766305895660844716785847696088000000000000)
      constant := (72277039503848904357418709182829022517499952193732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (623705681599537789/1250000000000000000)
  directionHi := (49896454527963023121/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree002.table
  base := (121132290176099150984127602722139072164659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-261521080479187230076309842475972848000000000000)
      constant := (42090281682381037502913637214697187970749869229186) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree002.table
  base := (241905210996223455275264849064446346606153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-261781609074579661127723881920406848000000000000)
      constant := (42028346324101092927726932391537540995749828475731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623705681599537789/1250000000000000000)
  centralHi := (49896454527963023121/100000000000000000000)
  directionLo := (17641060676944433917/25000000000000000000)
  directionHi := (70564242707777735669/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree003.table
  base := (152029413213711753619318571303451308021947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-129261219650058338277869972942155536000000000000)
      constant := (8879754396994994729786639022835665470763630134323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree003.table
  base := (30350720380705203872337451153402745311657/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-129391483947754553803576992664372536000000000000)
      constant := (8864048902044336108812093399127672341199022828565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17641060676944433917/25000000000000000000)
  centralHi := (70564242707777735669/100000000000000000000)
  directionLo := (86423194359982118269/100000000000000000000)
  directionHi := (8642319435998211827/10000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree004.table
  base := (103311564646528399030619100288405093299867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-514046237421162799590909995176960368000000000000)
      constant := (18443810086508428829238557641378194329175051050809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree004.table
  base := (25778736431432492008683182037515710571619/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-514567294611947661693738074065828368000000000000)
      constant := (18410895163173040541423715862333948958272513098052) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86423194359982118269/100000000000000000000)
  centralHi := (8642319435998211827/10000000000000000000)
  directionLo := (623705681599537789/625000000000000000)
  directionHi := (99792909055926046241/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree005.table
  base := (75255716846327657845984577505147969995547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-640308815892150584348210071527454128000000000000)
      constant := (13892965344200751597169092278827625277528183210169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree005.table
  base := (9389534133753033695105761353878915007873/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-640960137380631661976745170138539128000000000000)
      constant := (13870578417477656937142092138102527883774893009368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623705681599537789/625000000000000000)
  centralHi := (99792909055926046241/100000000000000000000)
  directionLo := (111571864160752500899/100000000000000000000)
  directionHi := (1115718641607525009/1000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree006.table
  base := (28900088942428355283144300726465175482501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-255523798121046123035170049292649296000000000000)
      constant := (3748205051508135617741417381372620940107670113818) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree006.table
  base := (57698209000207390244421228119303743078367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-255784326716438554086584088737083296000000000000)
      constant := (3743161276996668282394976811026755639255792090103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111571864160752500899/100000000000000000000)
  centralHi := (1115718641607525009/1000000000000000000)
  directionLo := (30555213391873171913/25000000000000000000)
  directionHi := (122220853567492687653/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree007.table
  base := (9206745532751024629308879738760220143917/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-892833972834126153862810224228441648000000000000)
      constant := (9648415021142011637734364111884163090740969000795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree007.table
  base := (9191118607874778664945954490149953293691/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-893745822917999662542759362283960648000000000000)
      constant := (9638316089785817976955294316771508701844692404285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30555213391873171913/25000000000000000000)
  centralHi := (122220853567492687653/100000000000000000000)
  directionLo := (132013609984832896041/100000000000000000000)
  directionHi := (66006804992416448021/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree008.table
  base := (9377798416852039395269321842458817634283/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-1019096551305113938620110300578935408000000000000)
      constant := (8680999884128322323637369453047044943217057804964) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree008.table
  base := (29958726592038620376641107810155479521/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-1020138665686683662825766458356671408000000000000)
      constant := (8674602785644498176279730242580541413997942833750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132013609984832896041/100000000000000000000)
  centralHi := (66006804992416448021/50000000000000000000)
  directionLo := (17641060676944433917/12500000000000000000)
  directionHi := (141128485415555471337/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree009.table
  base := (15488760771386448821374137992806148054903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-381786376592033907792470125643143056000000000000)
      constant := (2708355194245697041958586067521278717110452394654) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree009.table
  base := (30925081459258184840562663613460753621441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-382177169485122554369591184809794056000000000000)
      constant := (2707214168588426691814085038009667433956077043369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17641060676944433917/12500000000000000000)
  centralHi := (141128485415555471337/100000000000000000000)
  directionLo := (1871117044798613367/1250000000000000000)
  directionHi := (149689363583889069361/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree010.table
  base := (25759281768234805754528251537483995230043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-1271621708247089508134710453279922928000000000000)
      constant := (7864012356438910758249948662035227674982252368761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree010.table
  base := (6428574150694327921827253087232982065243/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-1272924351224051663391780650502092928000000000000)
      constant := (7863201415256784336596882450689662342437190236644) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1871117044798613367/1250000000000000000)
  centralHi := (149689363583889069361/100000000000000000000)
  directionLo := (157786443475384845001/100000000000000000000)
  directionHi := (78893221737692422501/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree011.table
  base := (21473054528036299524994016693453722055213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-1397884286718077292892010529630416688000000000000)
      constant := (7831453661037767955790551322741529899800650992351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree011.table
  base := (21433838280710466666182550385980845749701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-1399317193992735663674787746574803688000000000000)
      constant := (7833101508103494684798902952019266231292465425127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157786443475384845001/100000000000000000000)
  centralHi := (78893221737692422501/50000000000000000000)
  directionLo := (82743909019141551547/50000000000000000000)
  directionHi := (33097563607656620619/20000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree012.table
  base := (8942286457934008119040168135138207425789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-508048955063021692549770201993636816000000000000)
      constant := (2662275922798650999174848874180585501797646987402) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree012.table
  base := (8925048797442029909547923732266481225237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-508570012253806554652598280882504816000000000000)
      constant := (2663631661939907116176754731550352740848298679866) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82743909019141551547/50000000000000000000)
  centralHi := (33097563607656620619/20000000000000000000)
  directionLo := (172846388719964236539/100000000000000000000)
  directionHi := (8642319435998211827/5000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree013.table
  base := (14839801389747353638410720516043210001563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-1650409443660052862406610682331404208000000000000)
      constant := (8303464467701904151098571025857977435109292863801) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree013.table
  base := (2961877754933891881353745484411383754741/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-1652102879530103664240801938720225208000000000000)
      constant := (8309972198134841209857373820675882228156166446035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172846388719964236539/100000000000000000000)
  centralHi := (8642319435998211827/5000000000000000000)
  directionLo := (179904225264428021829/100000000000000000000)
  directionHi := (17990422526442802183/10000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree014.table
  base := (6115254329317606672208026735680591276929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-1776672022131040647163910758681897968000000000000)
      constant := (8762624243962735739557270471943700701911075419766) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree014.table
  base := (1525458077037036865895787367182881160741/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-1778495722298787664523809034792935968000000000000)
      constant := (8771625503519725753072300680165980418625619609656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179904225264428021829/100000000000000000000)
  centralHi := (17990422526442802183/10000000000000000000)
  directionLo := (37339087531676584029/20000000000000000000)
  directionHi := (93347718829191460073/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree015.table
  base := (1995303569572946904590879525633074163487/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-634311533534009477307070278344130576000000000000)
      constant := (3116808338122617642763513783873406770994107920915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree015.table
  base := (622052936979345079744146203399907797229/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-634962855022490554935605376955215576000000000000)
      constant := (3120663305487959835363918294551196396745017162576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37339087531676584029/20000000000000000000)
  centralHi := (93347718829191460073/50000000000000000000)
  directionLo := (48312034355399111757/25000000000000000000)
  directionHi := (193248137421596447029/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree016.table
  base := (4008064368530129590381845242467320703303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-2029197179073016216678510911382885488000000000000)
      constant := (10056183803654803140096645906698474825227581957562) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree016.table
  base := (7995292301050538754553480946090412903791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-2031281407836155665089823226938357488000000000000)
      constant := (10070392265184664960667410063936556851924814273557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48312034355399111757/25000000000000000000)
  centralHi := (193248137421596447029/100000000000000000000)
  directionLo := (623705681599537789/312500000000000000)
  directionHi := (199585818111852092481/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree017.table
  base := (6300630796795246776094309954122676297311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-2155459757544004001435810987733379248000000000000)
      constant := (10871466713569796686130726342910218223992837962597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree017.table
  base := (98161355743122091091239491318573085411/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-2157674250604839665372830323011068248000000000000)
      constant := (10888405014882881690594464182089660704778058323008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623705681599537789/312500000000000000)
  centralHi := (199585818111852092481/100000000000000000000)
  directionLo := (51432088090655032989/25000000000000000000)
  directionHi := (205728352362620131957/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree018.table
  base := (4790931634594194778678672462149645503427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-760574112004997262064370354694624336000000000000)
      constant := (3929835053709491513285196022277882267789796779643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree018.table
  base := (2387442904956766806694778451307716221039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-761355697791174555218612473027926336000000000000)
      constant := (3936421465964548843171865456547497445673958501902) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51432088090655032989/25000000000000000000)
  centralHi := (205728352362620131957/100000000000000000000)
  directionLo := (52923182030833301751/25000000000000000000)
  directionHi := (42338545624666641401/20000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree019.table
  base := (691066246839556351520410121032240976369/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-2407984914485979570950411140434366768000000000000)
      constant := (12804810503219745319892397613940087180450797013815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree019.table
  base := (3441293317723738990202632935675180101689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-2410459936142207665938844515156489768000000000000)
      constant := (12827485910245580014315376506921702568612621610403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52923182030833301751/25000000000000000000)
  centralHi := (42338545624666641401/20000000000000000000)
  directionLo := (43498720585672655747/20000000000000000000)
  directionHi := (13593350183022704921/6250000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree020.table
  base := (1133977695306598075860278219055018351627/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-2534247492956967355707711216784860528000000000000)
      constant := (13912902796495094120741794414097648095889838960658) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree020.table
  base := (451139437710150304458862386806606254839/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-2536852778910891666221851611229200528000000000000)
      constant := (13938593435497541647398893280218292719406044127265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43498720585672655747/20000000000000000000)
  centralHi := (13593350183022704921/6250000000000000000)
  directionLo := (223143728321505001799/100000000000000000000)
  directionHi := (1115718641607525009/500000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree021.table
  base := (3773736972396703575281416009875790589/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-886836690475985046821670431045118096000000000000)
      constant := (5036703324061578826238916778824616069520607008320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree021.table
  base := (149613771140226485446355707072409561877/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-887748540559858555501619569100637096000000000000)
      constant := (5046306181415539855950643271513651210557439885544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223143728321505001799/100000000000000000000)
  centralHi := (1115718641607525009/500000000000000000)
  directionLo := (114327139892156310253/50000000000000000000)
  directionHi := (228654279784312620507/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree022.table
  base := (16051227601437497640149062702531818507/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-2786772649898942925222311369485848048000000000000)
      constant := (16393413639261832132487280155865049538023684833424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree022.table
  base := (247519405820362961643923300268625539527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-2789638464448259666787865803374622048000000000000)
      constant := (16425446318826364456605772300371462328768320833629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114327139892156310253/50000000000000000000)
  centralHi := (228654279784312620507/100000000000000000000)
  directionLo := (117017558338635442569/50000000000000000000)
  directionHi := (234035116677270885139/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree023.table
  base := (-11974628752731925175050710574410932537/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-2913035228369930709979611445836341808000000000000)
      constant := (17760327762322024243312585374590210239823226155050) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree023.table
  base := (-60681434986309859698803534435881910977/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-2916031307216943667070872899447332808000000000000)
      constant := (17795694015477085962867835390644596227425154972210) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117017558338635442569/50000000000000000000)
  centralHi := (234035116677270885139/100000000000000000000)
  directionLo := (47858997905348949529/20000000000000000000)
  directionHi := (119647494763372373823/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree024.table
  base := (-1370901088212734156692390195736619521579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-1013099268946972831578970507395611856000000000000)
      constant := (6402933896037791360030095735335939068654205268189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree024.table
  base := (-344479237784417162845862302289089726509/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-1014141383328542555784626665173347856000000000000)
      constant := (6415871355937377641282802416660460541146245727276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47858997905348949529/20000000000000000000)
  centralHi := (119647494763372373823/50000000000000000000)
  directionLo := (30555213391873171913/12500000000000000000)
  directionHi := (48888341426997075061/20000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree025.table
  base := (-2069470594626692002311568761902912803563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-3165560385311906279494211598537329328000000000000)
      constant := (20737141853469662372860453746486658216491485082199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree025.table
  base := (-207555314302954655428766940090298612471/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-3168816992754311667636887091592754328000000000000)
      constant := (20779515776366836984067846478506082218431486160830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30555213391873171913/12500000000000000000)
  centralHi := (48888341426997075061/20000000000000000000)
  directionLo := (249482272639815115601/100000000000000000000)
  directionHi := (124741136319907557801/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree026.table
  base := (-2702526258733173401513691050576884806293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-3291822963782894064251511674887823088000000000000)
      constant := (22343948169993269654168396008829452961031160072489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree026.table
  base := (-2707794035167355986608593394666509771837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-3295209835522995667919894187665465088000000000000)
      constant := (22390001683174627467845141417600305517277108102001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249482272639815115601/100000000000000000000)
  centralHi := (124741136319907557801/50000000000000000000)
  directionLo := (63605748824294630087/25000000000000000000)
  directionHi := (254422995297178520349/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree027.table
  base := (-51199362357340248822710202358838793193/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-1139361847417960616336270583746105616000000000000)
      constant := (8009354039082710407085180804058413831973938052032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree027.table
  base := (-1640658452005092428516835310224880055177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-1140534226097226556067633761246058616000000000000)
      constant := (8025971887680602253731155246184683623039144109214) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63605748824294630087/25000000000000000000)
  centralHi := (254422995297178520349/100000000000000000000)
  directionLo := (259269583079946354809/100000000000000000000)
  directionHi := (25926958307994635481/10000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree028.table
  base := (-949427656135926232171776285894636566591/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-3544348120724869633766111827588810608000000000000)
      constant := (25788524268183249010866800815879708075472935483372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree028.table
  base := (-3801650479789279441943561248437669615027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-3547995521060363668485908379810886608000000000000)
      constant := (25842300453774924427588538059111129878494377527871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259269583079946354809/100000000000000000000)
  centralHi := (25926958307994635481/10000000000000000000)
  directionLo := (264027219969665792083/100000000000000000000)
  directionHi := (66006804992416448021/25000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree029.table
  base := (-4269973069583438891556502169255475650173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-3670610699195857418523411903939304368000000000000)
      constant := (27624539460826891042831270206377211750509123671729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree029.table
  base := (-4273376043359783575575628686791496390723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-3674388363829047668768915475883597368000000000000)
      constant := (27682362837622927544021348194810784180751366916879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264027219969665792083/100000000000000000000)
  centralHi := (66006804992416448021/25000000000000000000)
  directionLo := (268700630924773543783/100000000000000000000)
  directionHi := (33587578865596692973/12500000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree030.table
  base := (-4697355517359506944461962930320383651601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-1265624425888948401093570660096599376000000000000)
      constant := (9845149398040516250225140328496764156894586381191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree030.table
  base := (-587536569505174312798872546451801233183/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-1266927068865910556350640857318769376000000000000)
      constant := (9865815016721225183640964042724138238730975729224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268700630924773543783/100000000000000000000)
  centralHi := (33587578865596692973/12500000000000000000)
  directionLo := (13664706842248066517/5000000000000000000)
  directionHi := (273294136844961330341/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree031.table
  base := (-6353774125711753241431853312166071887/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-3923135856137832988038012056640291888000000000000)
      constant := (31520703104722357494003541070897142810856672520800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree031.table
  base := (-5085552432736116833675182175884539062637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-3927174049366415669334929668029018888000000000000)
      constant := (31587001272108192481126306365427516125287474690401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13664706842248066517/5000000000000000000)
  centralHi := (273294136844961330341/100000000000000000000)
  directionLo := (69452925338090300919/25000000000000000000)
  directionHi := (277811701352361203677/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree032.table
  base := (-5429589947466505789649973149437367335157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-4049398434608820772795312132990785648000000000000)
      constant := (33579849600194947394261815467269847801206526468361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree032.table
  base := (-217270932167846113867197125923978948069/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-4053566892135099669617936764101729648000000000000)
      constant := (33650578278420947594991483907802521222281698033425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69452925338090300919/25000000000000000000)
  centralHi := (277811701352361203677/100000000000000000000)
  directionLo := (282256970831110942673/100000000000000000000)
  directionHi := (141128485415555471337/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree033.table
  base := (-5739249366768898362009326204714463788317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-1391887004359936185850870736447093136000000000000)
      constant := (11904169965940950110164799029089191356705383240347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree033.table
  base := (-5741130109063570114109976867596833813043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-1393319911634594556633647953391480136000000000000)
      constant := (11929266497735642105009421912204992984209006763413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282256970831110942673/100000000000000000000)
  centralHi := (141128485415555471337/50000000000000000000)
  directionLo := (143316654438009833823/50000000000000000000)
  directionHi := (286633308876019667647/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree034.table
  base := (-6013811894402748658900383709298616148729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-4301923591550796342309912285691773168000000000000)
      constant := (37918369857628947481066116345240344525374748991517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree034.table
  base := (-3007715524951398700859455135494984782597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-4306352577672467670183950956247151168000000000000)
      constant := (37998351838439053769322449588550744416850523958962) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143316654438009833823/50000000000000000000)
  centralHi := (286633308876019667647/100000000000000000000)
  directionLo := (72735956518972090533/25000000000000000000)
  directionHi := (290943826075888362133/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree035.table
  base := (-1250957416722865719682058326874024457837/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-4428186170021784127067212362042266928000000000000)
      constant := (40197168110692851000359885120517953394465881900005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree035.table
  base := (-625618029679550471244515085035746129107/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-4432745420441151670466958052319861928000000000000)
      constant := (40281974877255432760016177511041950278536553917110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72735956518972090533/25000000000000000000)
  centralHi := (290943826075888362133/100000000000000000000)
  directionLo := (295191405881231336591/100000000000000000000)
  directionHi := (18449462867576958537/6250000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree036.table
  base := (-6463431593737756374877742019153700418683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-1518149582830923970608170812797586896000000000000)
      constant := (14182895691654070664336163047489940796172658096653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree036.table
  base := (-6464629795041847490610378001682162525533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-1519712754403278556916655049464190896000000000000)
      constant := (14212817281268922296625991702469571479996915495003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295191405881231336591/100000000000000000000)
  centralHi := (18449462867576958537/6250000000000000000)
  directionLo := (299378727167778138721/100000000000000000000)
  directionHi := (149689363583889069361/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree037.table
  base := (-6640792105423380819104026931717931460009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-4680711326963759696581812514743254448000000000000)
      constant := (44972745524771590603771315706661053749249220290957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree037.table
  base := (-3320911052728811435969593303110884655233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-4685531105978519671032972244465283448000000000000)
      constant := (45067602225749065290251129036642397589936351886218) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299378727167778138721/100000000000000000000)
  centralHi := (149689363583889069361/50000000000000000000)
  directionLo := (75877070999355604853/25000000000000000000)
  directionHi := (303508283997422419413/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree038.table
  base := (-212116901317585351740910852121891515447/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-4806973905434747481339112591093748208000000000000)
      constant := (47469192440530998238218527309243414965490754320992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree038.table
  base := (-6788625857377953956410647772707824334853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-4811923948747203671315979340537994208000000000000)
      constant := (47569275625796177883163019294514752550514423009369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75877070999355604853/25000000000000000000)
  centralHi := (303508283997422419413/100000000000000000000)
  directionLo := (307582402990680049649/100000000000000000000)
  directionHi := (6151648059813600993/2000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree039.table
  base := (-863125624279359125637072103773227749357/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-1644412161301911755365470889148080656000000000000)
      constant := (16679300638056291498743892518014936147387684919896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree039.table
  base := (-6905765110481505721613918146725842922681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-1646105597171962557199662145536901656000000000000)
      constant := (16714448892639600010447325539733535964690633389471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307582402990680049649/100000000000000000000)
  centralHi := (6151648059813600993/2000000000000000000)
  directionLo := (62320651730861154473/20000000000000000000)
  directionHi := (155801629327152886183/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree040.table
  base := (-699319110955698925562934554315162480471/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-5059499062376723050853712743794735728000000000000)
      constant := (52678768926021508151827442592426265051019265800830) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree040.table
  base := (-43711523060720140561301276308204301331/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-5064709634284571671881993532683415728000000000000)
      constant := (52789710833917074691042714070113926830763242378080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62320651730861154473/20000000000000000000)
  centralHi := (155801629327152886183/50000000000000000000)
  directionLo := (315572886950769690003/100000000000000000000)
  directionHi := (78893221737692422501/25000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree041.table
  base := (-3526402663278796281795215094382386800013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-5185761640847710835611012820145229488000000000000)
      constant := (55391705841648077832200968699191971282967091076098) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree041.table
  base := (-7053365368112347736331802357742870442601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-5191102477053255672165000628756126488000000000000)
      constant := (55508280868902350508668464092348126653325144586573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315572886950769690003/100000000000000000000)
  centralHi := (78893221737692422501/25000000000000000000)
  directionLo := (319493197349966042383/100000000000000000000)
  directionHi := (19968324834372877649/6250000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree042.table
  base := (-3542135084604822816919960648217193766021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-1770674739772899540122770965498574416000000000000)
      constant := (19392213167961473304627377072189297948311227406822) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree042.table
  base := (-3542375308621463472273973014876419536153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-1772498439940646557482669241609612416000000000000)
      constant := (19432994660356709350897647211779738308869750942846) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319493197349966042383/100000000000000000000)
  centralHi := (19968324834372877649/6250000000000000000)
  directionLo := (161682991782813561221/50000000000000000000)
  directionHi := (323365983565627122443/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree043.table
  base := (-7087938497381799655977795955559509996649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-5438286797789686405125612972846217008000000000000)
      constant := (61033508817434197333766201272169414872641432953677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree043.table
  base := (-443021907376284422210345644991211247981/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-5443888162590623672731014820901548008000000000000)
      constant := (61161759383138090131392182389418085340173958805008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161682991782813561221/50000000000000000000)
  centralHi := (323365983565627122443/100000000000000000000)
  directionLo := (327192933147747724873/100000000000000000000)
  directionHi := (163596466573873862437/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree044.table
  base := (-2759416055281491134764370188717756157/3906250000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-5564549376260674189882913049196710768000000000000)
      constant := (63962262741328203459247184783316022801351427484160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree044.table
  base := (-1412891664086536863996610553661359566247/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-5570281005359307673014021916974258768000000000000)
      constant := (64096556300857089318937635572915276609463370704655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327192933147747724873/100000000000000000000)
  centralHi := (163596466573873862437/50000000000000000000)
  directionLo := (82743909019141551547/25000000000000000000)
  directionHi := (330975636076566206189/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree045.table
  base := (-438313521573275088157704486502688375437/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-1896937318243887324880071041849068176000000000000)
      constant := (22320952873129005418161446641799399736007734852272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree045.table
  base := (-1753329763815975803389527346211404873317/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-1898891282709330557765676337682323176000000000000)
      constant := (22367777436268789952807044659713419684707157901388) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82743909019141551547/25000000000000000000)
  centralHi := (330975636076566206189/100000000000000000000)
  directionLo := (167357796241128751349/50000000000000000000)
  directionHi := (334715592482257502699/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree046.table
  base := (-6934878188584265372171177715482189874963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-5817074533202649759397513201897698288000000000000)
      constant := (70035260790988816788033570398055326552022179674399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree046.table
  base := (-1733784382657494813453681789316106547753/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-5823066690896675673580036109119680288000000000000)
      constant := (70182051945847851227726283779992228124984863924276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167357796241128751349/50000000000000000000)
  centralHi := (334715592482257502699/100000000000000000000)
  directionLo := (84603554899162539907/25000000000000000000)
  directionHi := (338414219596650159629/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree047.table
  base := (-341493143441010441732873180115460464187/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-5943337111673637544154813278248192048000000000000)
      constant := (73179439434452535155881728569922812388794897771020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree047.table
  base := (-3415042494180789631941907444572313147263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-5949459533665359673863043205192391048000000000000)
      constant := (73332685562618374385534361181776389619656715924598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84603554899162539907/25000000000000000000)
  centralHi := (338414219596650159629/100000000000000000000)
  directionLo := (342072858028331208027/100000000000000000000)
  directionHi := (85518214507082802007/25000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree048.table
  base := (-1674528616058360701516149179277359267001/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-2023199896714875109637371118199561936000000000000)
      constant := (25465123201195718519425830991767779339297456330364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree048.table
  base := (-6698304647710500208926335410400321898601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-2025284125478014558048683433755033936000000000000)
      constant := (25518402787224838226582863501898121256212485358191) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342072858028331208027/100000000000000000000)
  centralHi := (85518214507082802007/25000000000000000000)
  directionLo := (345692777439928473079/100000000000000000000)
  directionHi := (8642319435998211827/2500000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree049.table
  base := (-6539753531912084245643212415749023558791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-6195862268615613113669413430949179568000000000000)
      constant := (79683030424749403701542781106881944790931902041443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree049.table
  base := (-3269958162328856598896520583779288455241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-6202245219202727674429057397337812568000000000000)
      constant := (79849599597690680601988784211776309784191456394586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345692777439928473079/100000000000000000000)
  centralHi := (8642319435998211827/2500000000000000000)
  directionLo := (349275181695741161841/100000000000000000000)
  directionHi := (174637590847870580921/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree050.table
  base := (-24823753806096862332674152977712933021/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-6322124847086600898426713507299673328000000000000)
      constant := (83042404427354009746771185480333910066459955515648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree050.table
  base := (-635502028277868960275966816549258281709/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-6328638061971411674712064493410523328000000000000)
      constant := (83215841910707864480813003034338395566484286650570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349275181695741161841/100000000000000000000)
  centralHi := (174637590847870580921/50000000000000000000)
  directionLo := (352821213538888678341/100000000000000000000)
  directionHi := (176410606769444339171/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree051.table
  base := (-6143581264969827359050543881637847123861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-2149462475185862894394671194550055696000000000000)
      constant := (28824492328468530231622007049834046437214012586851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree051.table
  base := (-6143700444940344008538016019259233349053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-2151676968246698558331690529827744696000000000000)
      constant := (28884640256683356544496960374350770915466315395323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352821213538888678341/100000000000000000000)
  centralHi := (176410606769444339171/50000000000000000000)
  directionLo := (89082989712372686121/25000000000000000000)
  directionHi := (71266391769898148897/20000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree052.table
  base := (-1476481284938086501097558158645973244047/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-6574650004028576467941313660000660848000000000000)
      constant := (89976235851442561185649996131890356743880175521324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree052.table
  base := (-295301353653097664706234156125783847451/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-6581423747508779675278078685555944848000000000000)
      constant := (90163824010341857247686458910017246310957162712460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89082989712372686121/25000000000000000000)
  centralHi := (71266391769898148897/20000000000000000000)
  directionLo := (179904225264428021829/50000000000000000000)
  directionHi := (359808450528856043659/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree053.table
  base := (-5641971844580001833218853928456453263229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-6700912582499564252698613736351154608000000000000)
      constant := (93550670767443517459205640225495573657029850500017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree053.table
  base := (-5642059004948164743827671169743126740259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-6707816590277463675561085781628655608000000000000)
      constant := (93745541444215861096997862519929250929121565924207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179904225264428021829/50000000000000000000)
  centralHi := (359808450528856043659/100000000000000000000)
  directionLo := (363251672049059298801/100000000000000000000)
  directionHi := (181625836024529649401/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree054.table
  base := (-2675885506021144736902746737021636405507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-2275725053656850679151971270900549456000000000000)
      constant := (32398924379953916683098426168670803733286558299274) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree054.table
  base := (-2675922761061298361838056464970094380779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-2278069811015382558614697625900455456000000000000)
      constant := (32466354846303350140271446909717487464278238110778) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363251672049059298801/100000000000000000000)
  centralHi := (181625836024529649401/50000000000000000000)
  directionLo := (91665640175619515739/25000000000000000000)
  directionHi := (366662560702478062957/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree055.table
  base := (-2517682114772827997047126809917797199447/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-6953437739441539822213213889052142128000000000000)
      constant := (100914535768119504149970380837204817016312367609062) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree055.table
  base := (-2517713955051733980001198713007871652261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-6960602275814831676127099973774077128000000000000)
      constant := (101124386146116572461566873827641060241451417227506) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91665640175619515739/25000000000000000000)
  centralHi := (366662560702478062957/100000000000000000000)
  directionLo := (185021005290858456613/50000000000000000000)
  directionHi := (370042010581716913227/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree056.table
  base := (-4692786349899966632944576568223059025227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-7079700317912527606970513965402635888000000000000)
      constant := (104703952617688809676339697596731061552560722812471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree056.table
  base := (-2346420381107433986889463122143870041989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-7086995118583515676410107069846787888000000000000)
      constant := (104921500276235661702757416026800035613322798082994) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185021005290858456613/50000000000000000000)
  centralHi := (370042010581716913227/100000000000000000000)
  directionLo := (373390875316765840291/100000000000000000000)
  directionHi := (93347718829191460073/25000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree057.table
  base := (-108101664676009320212699757902042214457/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-2401987632127838463909271347251043216000000000000)
      constant := (36188339543458220381043615617410394819982519563480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree057.table
  base := (-33782133355048123577759775247497444127/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-2404462653784066558897704721973166216000000000000)
      constant := (36263467303224621967574685446034414926249558279296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373390875316765840291/100000000000000000000)
  centralHi := (93347718829191460073/25000000000000000000)
  directionLo := (94177492648284088079/25000000000000000000)
  directionHi := (376709970593136352317/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree058.table
  base := (-1964614716197608025617215453888678414031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-7332225474854503176485114118103623408000000000000)
      constant := (112497729565652121658503607915040063185258861163926) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree058.table
  base := (-196463456587556139978271020382304091163/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-7339780804120883676976121261992209408000000000000)
      constant := (112731086839058771761400057029227369863214719939980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94177492648284088079/25000000000000000000)
  centralHi := (376709970593136352317/100000000000000000000)
  directionLo := (76000015294404444481/20000000000000000000)
  directionHi := (190000038236011111203/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree059.table
  base := (-1754147710741442048987515702975196067931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-7458488053325490961242414194454117168000000000000)
      constant := (116502081867935269451862348788085758135681430893326) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree059.table
  base := (-219270582516591024538380999629132141371/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-7466173646889567677259128358064920168000000000000)
      constant := (116743551537266206616955087129393265307337677692528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76000015294404444481/20000000000000000000)
  centralHi := (190000038236011111203/50000000000000000000)
  directionLo := (383261939531182535957/100000000000000000000)
  directionHi := (191630969765591267979/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree060.table
  base := (-3061281775394403267395959556620999873079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-2528250210598826248666571423601536976000000000000)
      constant := (40192690851836277255217092950699671515336170504689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree060.table
  base := (-1530655357504106201899499764232617678899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-2530855496552750559180711818045876976000000000000)
      constant := (40275931015668851539365658877197456824278784888618) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383261939531182535957/100000000000000000000)
  centralHi := (191630969765591267979/50000000000000000000)
  directionLo := (48312034355399111757/12500000000000000000)
  directionHi := (386496274843192894057/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree061.table
  base := (-2588202937722315096597483078230102226893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-7711013210267466530757014347155104688000000000000)
      constant := (124725699127562586485005317531745043739895859796289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree061.table
  base := (-258822763854805694917214470193803198503/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-7718959332426935677825142550210341688000000000000)
      constant := (124983808888424057984406923385500387426082690108190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48312034355399111757/12500000000000000000)
  centralHi := (386496274843192894057/100000000000000000000)
  directionLo := (77940753561182863897/20000000000000000000)
  directionHi := (194851883902957159743/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree062.table
  base := (-2089071024088279063856432769622525819687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-7837275788738454315514314423505598448000000000000)
      constant := (128944959486358702376760477943178864563688572690051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree062.table
  base := (-417818420543472857695598533291239469247/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-7845352175195619678108149646283052448000000000000)
      constant := (129211596981751297253481035191888799793324035799655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77940753561182863897/20000000000000000000)
  centralHi := (194851883902957159743/50000000000000000000)
  directionLo := (78577015167690625047/20000000000000000000)
  directionHi := (98221268959613281309/25000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree063.table
  base := (-1563896198584711632321732908052823615003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-2654512789069814033423871499952030736000000000000)
      constant := (44411950624017806309419742918485993672278858321773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree063.table
  base := (-312782836525798623941952367198105749753/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-2657248339321434559463718914118587736000000000000)
      constant := (44503718527516906560384582596815627281667518545115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78577015167690625047/20000000000000000000)
  centralHi := (98221268959613281309/25000000000000000000)
  directionLo := (633665327927197901/160000000000000000)
  directionHi := (198020414977249344063/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree064.table
  base := (-50634349454135972227036217599990375459/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-8089800945680429885028914576206585968000000000000)
      constant := (137598374808103613295349787872076421296481742676140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree064.table
  base := (-253175582473856652353630298460906066681/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-8098137860732987678674163838428473968000000000000)
      constant := (137882483227482866578485923210014012633083897921652) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (633665327927197901/160000000000000000)
  centralHi := (198020414977249344063/50000000000000000000)
  directionLo := (399171636223704184961/100000000000000000000)
  directionHi := (199585818111852092481/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree065.table
  base := (-435450551389409738171135595192132195913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-8216063524151417669786214652557079728000000000000)
      constant := (142032527055529751141369040260140156866589026968749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree065.table
  base := (-10886590874692220149400797614608067047/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-8224530703501671678957170934501184728000000000000)
      constant := (142325578688880703891745792908159465347250002373240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399171636223704184961/100000000000000000000)
  centralHi := (199585818111852092481/50000000000000000000)
  directionLo := (201139038565348067481/50000000000000000000)
  directionHi := (402278077130696134963/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree066.table
  base := (16780710940406996270179004503081647813/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-2780775367540801818181171576302524496000000000000)
      constant := (48846102524863657584954602222868287135822734375170) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree066.table
  base := (83897976482120746054327077331921982089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-2783641182090118559746726010191298496000000000000)
      constant := (48946813645564223083106664857630554724060750440802) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201139038565348067481/50000000000000000000)
  centralHi := (402278077130696134963/100000000000000000000)
  directionLo := (405360712840343458927/100000000000000000000)
  directionHi := (25335044552521466183/6250000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree067.table
  base := (159416190682353557227632572839152024673/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-8468588681093393239300814805258067248000000000000)
      constant := (151115715492665160716759723844013955163477334198855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree067.table
  base := (797071441991882237195954183980630033433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-8477316389039039679523185126646606248000000000000)
      constant := (151427069106593230587187950532390722435481707508291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405360712840343458927/100000000000000000000)
  centralHi := (25335044552521466183/6250000000000000000)
  directionLo := (51052510297133723567/12500000000000000000)
  directionHi := (408420082377069788537/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree068.table
  base := (726183375225054155973338772851597689491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-8594851259564381024058114881608561008000000000000)
      constant := (155764750077324679976406988226509143456128431454914) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree068.table
  base := (1452358642929994850182980921764549458291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-8603709231807723679806192222719317008000000000000)
      constant := (156085462473256800061538892121165765651409605645057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51052510297133723567/12500000000000000000)
  centralHi := (408420082377069788537/100000000000000000000)
  directionLo := (411456704725240263913/100000000000000000000)
  directionHi := (205728352362620131957/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree069.table
  base := (2133660949667578351566133899717166587321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-2907037946011789602938471652653018256000000000000)
      constant := (53495136904587880314168351376076405440741778408289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree069.table
  base := (266706755003742997059100759152863695563/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-2910034024858802560029733106264009256000000000000)
      constant := (53605206809318437875410539296656259904775795738136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411456704725240263913/100000000000000000000)
  centralHi := (205728352362620131957/50000000000000000000)
  directionLo := (414471079856984274239/100000000000000000000)
  directionHi := (1295222124553075857/312500000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree070.table
  base := (2840960570228091582403104563777127365571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-8847376416506356593572715034309548528000000000000)
      constant := (165277696885870464471109532526647656100864971637617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree070.table
  base := (2840954682488120619248246472794327558117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-8856494917345091680372206414864738528000000000000)
      constant := (165617542459777112176310968016464391540707407423559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414471079856984274239/100000000000000000000)
  centralHi := (1295222124553075857/312500000000000000)
  directionLo := (417463689693218369449/100000000000000000000)
  directionHi := (8349273793864367389/2000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree071.table
  base := (178713155481736005838166884275476663549/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 343470000000000000000000000000000000000000000
      center := (5289438)
      previous := (2644719)
      next := (2644719)
      square := (23557656090414188029269482158680000000000000)
      linear := (-1780130727033791783045033745419568000000000000)
      constant := (33751558849505010297591499120550243939258350060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree071.table
  base := (14297032373981475733839997462101970571/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 343470000000000000000000000000000000000000000
      center := (5289438)
      previous := (2644719)
      next := (2644719)
      square := (23557656090414188029269482158680000000000000)
      linear := (-1781965435452048339745132614746568000000000000)
      constant := (33820914132092732752552905028280102095800534250) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417463689693218369449/100000000000000000000)
  centralHi := (8349273793864367389/2000000000000000000)
  directionLo := (42043499900310011981/10000000000000000000)
  directionHi := (420434999003100119811/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree072.table
  base := (433356646683666570693370800115465883299/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-3033300524482777387695771729003512016000000000000)
      constant := (58359048057811267653372567289981667364142647552910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree072.table
  base := (433356219396691693364840836249843631099/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-3036426867627486560312740202336720016000000000000)
      constant := (58478892369427642628678204865922388327112928054910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42043499900310011981/10000000000000000000)
  centralHi := (420434999003100119811/100000000000000000000)
  directionLo := (423385456246666414009/100000000000000000000)
  directionHi := (42338545624666641401/10000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree073.table
  base := (5118868877727313099343315946361520829267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-9226164151919319947844615263361029808000000000000)
      constant := (180084304619664490483935708112536699889007004424609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree073.table
  base := (255943261928750271643801307012087363483/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-9235673445651143681221227703082870808000000000000)
      constant := (180453889062795818019251983190357549496387371592820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423385456246666414009/100000000000000000000)
  centralHi := (42338545624666641401/10000000000000000000)
  directionLo := (426315494364981956239/100000000000000000000)
  directionHi := (5328943679562274453/1250000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree074.table
  base := (148254221525751113581013435068503163391/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-9352426730390307732601915339711523568000000000000)
      constant := (185163089242573805804602147919119799702769040110280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree074.table
  base := (2965082881046637241261967726876043463699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-9362066288419827681504234799155581568000000000000)
      constant := (185542863749724115958303866500285320540594204433346) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426315494364981956239/100000000000000000000)
  centralHi := (5328943679562274453/1250000000000000000)
  directionLo := (85845106304347959321/20000000000000000000)
  directionHi := (214612765760869898303/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree075.table
  base := (211483286652930008694195453990806197903/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-3159563102953765172453071805354005776000000000000)
      constant := (63437832608932451867366837833250637476656277898464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree075.table
  base := (6767462534385525760851709127040016206011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-3162819710396170560595747298409430776000000000000)
      constant := (63567866985359356892084047569980389904680347112499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85845106304347959321/20000000000000000000)
  centralHi := (214612765760869898303/50000000000000000000)
  directionLo := (432115971799910591349/100000000000000000000)
  directionHi := (8642319435998211827/2000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree076.table
  base := (7630756768792214638994585124695071512451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-9604951887332283302116515492412511088000000000000)
      constant := (195535530191482495015751215625010191480661536819377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree076.table
  base := (763075452264216793488253400878556315423/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-9614851973957195682070248991301003088000000000000)
      constant := (195936100503033696653153974874129517763535680900210) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432115971799910591349/100000000000000000000)
  centralHi := (8642319435998211827/2000000000000000000)
  directionLo := (43498720585672655747/10000000000000000000)
  directionHi := (434987205856726557471/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree077.table
  base := (8520042771549070731685589406158675685807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-9731214465803271086873815568763004848000000000000)
      constant := (200829186184752082427705954677880661758287062079189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree077.table
  base := (8520040859694169284979565452293271887091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-9741244816725879682353256087373713848000000000000)
      constant := (201240362240446549382606080442623838570919315382657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43498720585672655747/10000000000000000000)
  centralHi := (434987205856726557471/100000000000000000000)
  directionLo := (437839611540005924089/100000000000000000000)
  directionHi := (43783961154000592409/10000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree078.table
  base := (4717661222250640149331828168039711664063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-3285825681424752957210371881704499536000000000000)
      constant := (68731488559685966816994350430731498062443605167534) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree078.table
  base := (2358830204355985813985650407054577473369/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-3289212553164854560878754394482141536000000000000)
      constant := (68872128680749333430996427613213354846480820295684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437839611540005924089/100000000000000000000)
  centralHi := (43783961154000592409/10000000000000000000)
  directionLo := (27542097154285670373/6250000000000000000)
  directionHi := (440673554468570725969/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree079.table
  base := (10376595168973086253313043780361331503867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-9983739622745246656388415721463992368000000000000)
      constant := (211631368567280432036937737365854443554596295358809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree079.table
  base := (10376593784451331863075506857565057873003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-9994030502263247682919270279519135368000000000000)
      constant := (212064171802581715907063476519287058024573495600681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27542097154285670373/6250000000000000000)
  centralHi := (440673554468570725969/100000000000000000000)
  directionLo := (443489388579282077187/100000000000000000000)
  directionHi := (110872347144820519297/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree080.table
  base := (11343860425366696751460249099908844444239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-10110002201216234441145715797814486128000000000000)
      constant := (217139894759454838763595531504034488972916562019253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree080.table
  base := (2835964811851445559502536597060600566473/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-10120423345031931683202277375591846128000000000000)
      constant := (217583719432561062054425296406616918626548652913484) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443489388579282077187/100000000000000000000)
  centralHi := (110872347144820519297/25000000000000000000)
  directionLo := (223143728321505001799/50000000000000000000)
  directionHi := (446287456643010003599/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree081.table
  base := (12337117777287728718288867990937415888073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-3412088259895740741967671958054993296000000000000)
      constant := (74240014726674129633569513011013561929967343343857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree081.table
  base := (12337116775207152669559738032804494048649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-3415605395933538561161761490554852296000000000000)
      constant := (74391676285849143967860853677983051052561794283441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223143728321505001799/50000000000000000000)
  centralHi := (446287456643010003599/100000000000000000000)
  directionLo := (449068090751667208081/100000000000000000000)
  directionHi := (224534045375833604041/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree082.table
  base := (13356366858217405547113022011061282389249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-10362527358158210010660315950515473648000000000000)
      constant := (228371816765522838710503057184028629343632841966523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree082.table
  base := (1335636600587086111624801058753555077341/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-10373209030569299683768291567737267648000000000000)
      constant := (228838100014865646795627820961145236654130553194070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449068090751667208081/100000000000000000000)
  centralHi := (224534045375833604041/50000000000000000000)
  directionLo := (90366322555653153487/20000000000000000000)
  directionHi := (112957903194566441859/25000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree083.table
  base := (7200803680161088472874072361538742812919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-10488789936629197795417616026865967408000000000000)
      constant := (234095212462656893916523457244465106576303705899226) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree083.table
  base := (14401606635431246809469068749240919317859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-10499601873337983684051298663809978408000000000000)
      constant := (234572932851886111327897351184185903465140745990993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90366322555653153487/20000000000000000000)
  centralHi := (112957903194566441859/25000000000000000000)
  directionLo := (227289167405900461453/50000000000000000000)
  directionHi := (454578334811800922907/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree084.table
  base := (7736419512528691132854570072051112273749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-3538350838366728526724972034405487056000000000000)
      constant := (79963410408886432550157039011489626469344139498682) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree084.table
  base := (3094567681728503273607582249432884690253/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-3541998238702222561444768586627563056000000000000)
      constant := (80126509108138248385399179833017776169315499777385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227289167405900461453/50000000000000000000)
  centralHi := (454578334811800922907/100000000000000000000)
  directionLo := (114327139892156310253/25000000000000000000)
  directionHi := (457308559568625241013/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree085.table
  base := (3314012327055374168151518238492634225877/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-10741315093571173364932216179566954928000000000000)
      constant := (245756873019932664655365317069147278407994953425395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree085.table
  base := (1035628819448221785189286264913240892639/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-10752387558875351684617312855955399928000000000000)
      constant := (246257883395341220017969939820797478080878032096848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114327139892156310253/25000000000000000000)
  centralHi := (457308559568625241013/100000000000000000000)
  directionLo := (230011290390924039827/50000000000000000000)
  directionHi := (92004516156369615931/20000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree086.table
  base := (17693275008606854497130531201243790885559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-10867577672042161149689516255917448688000000000000)
      constant := (251695137810900208726586300566696940655638872958893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree086.table
  base := (8846637281521429237059518446695082587287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-10878780401644035684900319952028110688000000000000)
      constant := (252208001033503999673220156467139423056388760710298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230011290390924039827/50000000000000000000)
  centralHi := (92004516156369615931/20000000000000000000)
  directionLo := (46272068357017824563/10000000000000000000)
  directionHi := (462720683570178245631/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree087.table
  base := (18842478991881146637773616732094104594371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-3664613416837716311482272110755980816000000000000)
      constant := (85901675191014080683145309936611891731048306991739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree087.table
  base := (9421239306567306469227635453109058798163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-3668391081470906561727775682700273816000000000000)
      constant := (86076626737579120752658676521310504884164455661334) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46272068357017824563/10000000000000000000)
  centralHi := (462720683570178245631/100000000000000000000)
  directionLo := (465403144787520860491/100000000000000000000)
  directionHi := (116350786196880215123/25000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree088.table
  base := (2502209182058443908933931309658920088689/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-11120102828984136719204116408618436208000000000000)
      constant := (263786536284086971113898707256613789931925917275224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree088.table
  base := (20017673134556950556333850570127351947461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-11131566087181403685466334144173532208000000000000)
      constant := (264323520911071187695910170102455132701148131996647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465403144787520860491/100000000000000000000)
  centralHi := (116350786196880215123/25000000000000000000)
  directionLo := (468070233354541770277/100000000000000000000)
  directionHi := (234035116677270885139/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree089.table
  base := (21218858294342518867420124736514263321979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-11246365407455124503961416484968929968000000000000)
      constant := (269939669925330849962216908423597895355095184086233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree089.table
  base := (106094290103855001475268744365490805303/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-11257958929950087685749341240246242968000000000000)
      constant := (270488923110058992055483899739635017315798026556200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468070233354541770277/100000000000000000000)
  centralHi := (234035116677270885139/50000000000000000000)
  directionLo := (470722210573323456007/100000000000000000000)
  directionHi := (58840276321665432001/12500000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree090.table
  base := (4489206682958826757037557232713380017847/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-3790875995308704096239572187106474576000000000000)
      constant := (92054808827022574931018130182942164810612245287115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree090.table
  base := (22446033182329757900356491665870188237107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-3794783924239590562010782778772984576000000000000)
      constant := (92242028931404544124877392589724050224823382374763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470722210573323456007/100000000000000000000)
  centralHi := (58840276321665432001/12500000000000000000)
  directionLo := (118339832606538633751/25000000000000000000)
  directionHi := (94671866085230907001/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree091.table
  base := (23699198741652752067099438956176343206883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-11498890564397100073476016637669917488000000000000)
      constant := (282460805938109337652138253441886061371899251231441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree091.table
  base := (23699198544141076510566303164910220668971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-11510744615487455686315355432391664488000000000000)
      constant := (283035011950533412023366537744177138849907737709417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118339832606538633751/25000000000000000000)
  centralHi := (94671866085230907001/20000000000000000000)
  directionLo := (118995459964854970141/25000000000000000000)
  directionHi := (95196367971883976113/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree092.table
  base := (24978354210964764919513049345892950868301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-11625153142868087858233316714020411248000000000000)
      constant := (288828808285382554334641738293264254405890087147327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree092.table
  base := (24978354043169049797383739153122200297333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-11637137458256139686598362528464375248000000000000)
      constant := (289415698568104090763135492470595481780820595113591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118995459964854970141/25000000000000000000)
  centralHi := (95196367971883976113/20000000000000000000)
  directionLo := (478589979053489495291/100000000000000000000)
  directionHi := (119647494763372373823/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree093.table
  base := (13141749884519260971807875380686553809723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-3917138573779691880996872263456968336000000000000)
      constant := (98422811171197009742519516138559404742749722797414) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree093.table
  base := (26283499626503509208187849879229190808717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-3921176767008274562293789874845695336000000000000)
      constant := (98622715545921543756541443800228747781073333703253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478589979053489495291/100000000000000000000)
  centralHi := (119647494763372373823/25000000000000000000)
  directionLo := (481183981679440982959/100000000000000000000)
  directionHi := (6014799770993012287/1250000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree094.table
  base := (27614635370802827894955168775204948623227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-11877678299810063427747916866721398768000000000000)
      constant := (301779681614930990141517145852953573302994729933529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree094.table
  base := (27614635249738637562891015825144910290749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-11889923143793507687164376720609796768000000000000)
      constant := (302392356151826467058700643948339779822365790107023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481183981679440982959/100000000000000000000)
  centralHi := (6014799770993012287/1250000000000000000)
  directionLo := (12094101878584806607/2500000000000000000)
  directionHi := (483764075143392264281/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree095.table
  base := (7242940244606994625205748195806292626861/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-12003940878281051212505216943071892528000000000000)
      constant := (308362552582852480002285125677367177649284081681788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree095.table
  base := (3621470109451396012171997563867314886459/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-12016315986562191687447383816682507528000000000000)
      constant := (308988327103837715874263320520234204904133198905544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12094101878584806607/2500000000000000000)
  centralHi := (483764075143392264281/100000000000000000000)
  directionLo := (486330480819167614381/100000000000000000000)
  directionHi := (243165240409583807191/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree096.table
  base := (30354876560167318956327027624823001289503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-4043401152250679665754172339807462096000000000000)
      constant := (105005682137286260183496132610565698305029903548727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree096.table
  base := (30354876472856583363209292604202540263293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-4047569609776958562576796970918406096000000000000)
      constant := (105218686496128379424897595752643012783594659888837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486330480819167614381/100000000000000000000)
  centralHi := (243165240409583807191/50000000000000000000)
  directionLo := (30555213391873171913/6250000000000000000)
  directionHi := (488883414269970750609/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree097.table
  base := (15881991044692019967819580291810126464473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-12256466035223026782019817095772880048000000000000)
      constant := (321743163097337908662469388432909869870673912148742) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree097.table
  base := (31763982015248397256263318835099543786703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-12269101672099559688013398008827929048000000000000)
      constant := (322395553300927795823049727717212065763457557110581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30555213391873171913/6250000000000000000)
  centralHi := (488883414269970750609/100000000000000000000)
  directionLo := (98284617091938639189/20000000000000000000)
  directionHi := (245711542729846597973/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree098.table
  base := (16599538771866788626894560212709862107769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-12382728613694014566777117172123373808000000000000)
      constant := (328540902635421054389333719820451326344128292861126) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree098.table
  base := (1037471171274725041815646055728539785979/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-12395494514868243688296405104900639808000000000000)
      constant := (329206808537657332523120062148966979129353389255456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98284617091938639189/20000000000000000000)
  centralHi := (245711542729846597973/50000000000000000000)
  directionLo := (493949698954444149677/100000000000000000000)
  directionHi := (246974849477222074839/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree099.table
  base := (34660162904476726282930519335203919960283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-4169663730721667450511472416157955856000000000000)
      constant := (111803421674287883790134244782578618718991036817747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree099.table
  base := (17330081425521427925030075592873420076551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-4173962452545642562859804066991116856000000000000)
      constant := (112029941731793538928101396033696190737053751446718) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (493949698954444149677/100000000000000000000)
  centralHi := (246974849477222074839/50000000000000000000)
  directionLo := (496463454114849309283/100000000000000000000)
  directionHi := (124115863528712327321/25000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree100.table
  base := (36147238155902566479098355631277557018633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-12635253770635990136291717324824361328000000000000)
      constant := (342351250256945460123553736248534311154882616748691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree100.table
  base := (36147238110545150922952328838577296986477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-12648280200405611688862419297046061328000000000000)
      constant := (343044603271421164266207401138941488089176003141279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (496463454114849309283/100000000000000000000)
  centralHi := (124115863528712327321/25000000000000000000)
  directionLo := (249482272639815115601/50000000000000000000)
  directionHi := (498964545279630231203/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree101.table
  base := (18830151642421818537427410225525282031887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-12761516349106977921049017401174855088000000000000)
      constant := (349363858335386624000116646774568646810172064158698) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree101.table
  base := (18830151623172787840239891460108163875751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-12774673043174295689145426393118772088000000000000)
      constant := (350071142763536335437954967490269253482984710376954) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249482272639815115601/50000000000000000000)
  centralHi := (498964545279630231203/100000000000000000000)
  directionLo := (125363290485235661179/25000000000000000000)
  directionHi := (501453161940942644717/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree102.table
  base := (39199358280268614641694764003768438859229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-4295926309192655235268772492508449616000000000000)
      constant := (118816029752092381354533126834983084613613035930661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree102.table
  base := (1959967912379780695877824860384508601351/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-4300355295314326563142811163063827616000000000000)
      constant := (119056481223282594398545500164550613325647791331180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125363290485235661179/25000000000000000000)
  centralHi := (501453161940942644717/100000000000000000000)
  directionLo := (503929488911921417219/100000000000000000000)
  directionHi := (25196474445596070861/5000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree103.table
  base := (40764403132940102837290982288644810024119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-13014041506048953490563617553875842608000000000000)
      constant := (363603943018017627702213408649092669368377911492013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree103.table
  base := (40764403105213320126892680247905712328149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-13027458728711663689711440585264193608000000000000)
      constant := (364339505988783030186681693632743686078229400796823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (503929488911921417219/100000000000000000000)
  centralHi := (25196474445596070861/5000000000000000000)
  directionLo := (1012787412973702813/200000000000000000)
  directionHi := (506393706486851406501/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree104.table
  base := (21177718917563563205792548967823859199883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-13140304084519941275320917630226336368000000000000)
      constant := (370831419619269508913306491810767786890922761284882) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree104.table
  base := (42355437811599890439142092166933281900683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-13153851571480347689994447681336904368000000000000)
      constant := (371581329719026394987811852555456536113984948124041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1012787412973702813/200000000000000000)
  centralHi := (506393706486851406501/100000000000000000000)
  directionLo := (508845990594357040697/100000000000000000000)
  directionHi := (254422995297178520349/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree105.table
  base := (8794492476072717207541620679415202435731/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-4422188887663643020026072568858943376000000000000)
      constant := (126043506352971075464440667405626090850967875739895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree105.table
  base := (21986231180200794804419345728335612848149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-4426748138083010563425818259136538376000000000000)
      constant := (126298304953159257125041116572053907628367452557882) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (508845990594357040697/100000000000000000000)
  centralHi := (254422995297178520349/50000000000000000000)
  directionLo := (255643256471989485373/50000000000000000000)
  directionHi := (511286512943978970747/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree106.table
  base := (45615476763245328612943214733178623162011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-13392829241461916844835517782927323888000000000000)
      constant := (385501241336013087634853493429033852829687528349497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree106.table
  base := (11403869186577444484223523907222592185743/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-13406637257017715690560461873482325888000000000000)
      constant := (386280261409218004340135713612636957521378105650644) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255643256471989485373/50000000000000000000)
  centralHi := (511286512943978970747/100000000000000000000)
  directionLo := (256857720583241695009/50000000000000000000)
  directionHi := (513715441166483390019/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree107.table
  base := (9456896195851932406209978865113310802461/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (2328942)
      previous := (1164471)
      next := (1164471)
      square := (10372446881979030645082318068120000000000000)
      linear := (-1180809836661097443409277479192752000000000000)
      constant := (34321214643181740812662158435301926996328088515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree107.table
  base := (9456896192978588656990175284715366315789/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (2328942)
      previous := (1164471)
      next := (1164471)
      square := (10372446881979030645082318068120000000000000)
      linear := (-1182027260004052728696258971923752000000000000)
      constant := (34390546717397135782227624127567686423968385235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256857720583241695009/50000000000000000000)
  centralHi := (513715441166483390019/100000000000000000000)
  directionLo := (129033234737057117939/25000000000000000000)
  directionHi := (516132938948228471757/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree108.table
  base := (48979475024642129898929058701392245897271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-4548451466134630804783372645209437136000000000000)
      constant := (133485851466528475017822240621286935797143670477839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree108.table
  base := (48979475012455618624351263838646768414003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-4553140980851694563708825355209249136000000000000)
      constant := (133755412911207778660091502337011194046774050469227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129033234737057117939/25000000000000000000)
  centralHi := (516132938948228471757/100000000000000000000)
  directionLo := (518539166159892709619/100000000000000000000)
  directionHi := (25926958307994635481/5000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree109.table
  base := (5070045889625619034722694217672391195113/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-13771616976874880199107418011978805168000000000000)
      constant := (408043145184863040121865979848183176835282514496510) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree109.table
  base := (10140091777183976937313531685489462982601/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-13785815785323767691409483161700458168000000000000)
      constant := (408866869507115668694188680629413487058522909967135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (518539166159892709619/100000000000000000000)
  centralHi := (25926958307994635481/5000000000000000000)
  directionLo := (508724881816261371/97656250000000000)
  directionHi := (104186855795970328781/20000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree110.table
  base := (2097897303659685569208950190691924981619/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-13897879555345867983864718088329298928000000000000)
      constant := (415700358805168743172061623203101221433985733612825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree110.table
  base := (52447432582725845270597625506382870566399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-13912208628092451691692490257773168928000000000000)
      constant := (416539261687513577023439987315687690387389640629573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (508724881816261371/97656250000000000)
  centralHi := (104186855795970328781/20000000000000000000)
  directionLo := (261659215006236204963/50000000000000000000)
  directionHi := (523318430012472409927/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree111.table
  base := (6777549513522775354918029770789816132737/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-4674714044605618589540672721559930896000000000000)
      constant := (141143065086709066289581724711005888106556652059464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree111.table
  base := (54220396100748040627831831092654119100329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-4679533823620378563991832451281959896000000000000)
      constant := (141427805091483017336098532740584518671291099940561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261659215006236204963/50000000000000000000)
  centralHi := (523318430012472409927/100000000000000000000)
  directionLo := (525691768401579658627/100000000000000000000)
  directionHi := (131422942100394914657/25000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree112.table
  base := (1750604670141538018164088562739388322207/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-14150404712287843553379318241030286448000000000000)
      constant := (431229654549427240334776025082120827587617143743648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree112.table
  base := (28009674719112624863700832307669192199371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-14164994313629819692258504449918590448000000000000)
      constant := (432099330267617150156010655500355219427764644620434) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (525691768401579658627/100000000000000000000)
  centralHi := (131422942100394914657/25000000000000000000)
  directionLo := (264027219969665792083/50000000000000000000)
  directionHi := (528054439939331584167/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree113.table
  base := (7230536574880839857011233490067245671007/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-14276667290758831338136618317380780208000000000000)
      constant := (439101736672811496811943928142045654483839458556712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree113.table
  base := (28922146296850769958527815069725457180737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-14291387156398503692541511545991301208000000000000)
      constant := (439987006666765786588879666329732038454646252836598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264027219969665792083/50000000000000000000)
  centralHi := (528054439939331584167/100000000000000000000)
  directionLo := (132601646792682741973/25000000000000000000)
  directionHi := (530406587170730967893/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree114.table
  base := (59695225570508636178289519222035834312279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-4800976623076606374297972797910424656000000000000)
      constant := (149015147210022560660139280113162281378155103928111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree114.table
  base := (5969522556597676497351967780417671069589/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-4805926666389062564274839547354670656000000000000)
      constant := (149315481490562388038977699737207867813377270079010) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132601646792682741973/25000000000000000000)
  centralHi := (530406587170730967893/100000000000000000000)
  directionLo := (532748349493983238423/100000000000000000000)
  directionHi := (66593543686747904803/12500000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree115.table
  base := (12314429671581405392754027844139477153981/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-14529192447700806907651218470081767728000000000000)
      constant := (455060769421021277581702719474979265282665231183435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree115.table
  base := (61572148354065000225901957247640356422721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-14544172841935871693107525738136722728000000000000)
      constant := (455977643682210576561073826206373686916460090060667) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (532748349493983238423/100000000000000000000)
  centralHi := (66593543686747904803/12500000000000000000)
  directionLo := (535079863256901485431/100000000000000000000)
  directionHi := (66884982907112685679/12500000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree116.table
  base := (3173753048020829811333679295960212968767/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-14655455026171794692408518546432261488000000000000)
      constant := (463147720045529389378720167478882991668391371822180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree116.table
  base := (15868765239289911276572090130160262218633/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-14670565684704555693390532834209433488000000000000)
      constant := (464080604298196366496073166004831309838801188594764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535079863256901485431/100000000000000000000)
  centralHi := (66884982907112685679/12500000000000000000)
  directionLo := (268700630924773543783/50000000000000000000)
  directionHi := (537401261849547087567/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree117.table
  base := (8175495422170612391298265223539893836907/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-4927239201547594159055272874260918416000000000000)
      constant := (157102097834491862700826464694284956517758639143704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree117.table
  base := (65403963374604126498466910603560597165937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-4932319509157746564557846643427381416000000000000)
      constant := (157418442106510284244609576963256645443119128886233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268700630924773543783/50000000000000000000)
  centralHi := (537401261849547087567/100000000000000000000)
  directionLo := (33732042237080254093/6250000000000000000)
  directionHi := (539712675793284065489/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree118.table
  base := (67358855608207324175128640260311861406741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-14907980183113770261923118699133249008000000000000)
      constant := (479536489794765577960447334988581198334339896293207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree118.table
  base := (33679427802933653402119115664640349052219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-14923351370241923693956547026354855008000000000000)
      constant := (480501809746122072396607251482227812082615178341426) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33732042237080254093/6250000000000000000)
  centralHi := (539712675793284065489/100000000000000000000)
  directionLo := (271007116413207698141/50000000000000000000)
  directionHi := (542014232826415396283/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree119.table
  base := (8667467206563261503839169762405662129461/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-15034242761584758046680418775483742768000000000000)
      constant := (487838308919323560426681378890615327105332554485176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree119.table
  base := (6933973765052284392198913402630096019011/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-15049744213010607694239554122427565768000000000000)
      constant := (488820054577896207237129458389861516382514178884970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271007116413207698141/50000000000000000000)
  centralHi := (542014232826415396283/100000000000000000000)
  directionLo := (544306057986560277281/100000000000000000000)
  directionHi := (272153028993280138641/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree120.table
  base := (71346609509912628051002567621862898402407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-5053501780018581943812572950611412176000000000000)
      constant := (165403916959029727387366286664765173780321964182463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree120.table
  base := (71346609508231870697334249977942603926503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-5058712351926430564840853739500092176000000000000)
      constant := (165736686938264861567586920557160145541539200081727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544306057986560277281/100000000000000000000)
  centralHi := (272153028993280138641/50000000000000000000)
  directionLo := (13664706842248066517/2500000000000000000)
  directionHi := (546588273689922660681/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree121.table
  base := (1834486779503819226081092001192604477701/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-15286767918526733616195018928184730288000000000000)
      constant := (504656815668014973666781972065568857880152027245080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree121.table
  base := (36689735589364231262702735043354264945259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-15302529898547975694805568314572987288000000000000)
      constant := (505671828456771161749275597008555867391670243221586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13664706842248066517/2500000000000000000)
  centralHi := (546588273689922660681/100000000000000000000)
  directionLo := (274430499903796627161/50000000000000000000)
  directionHi := (548860999807593254323/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree122.table
  base := (18859580665753587756286511450089399343703/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-15413030496997721400952319004535224048000000000000)
      constant := (513173503292064200184183741184849259299441678198324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree122.table
  base := (75438322661807446736969417714334624364727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-15428922741316659695088575410645698048000000000000)
      constant := (514205357503790414118630693953832348356341657754029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274430499903796627161/50000000000000000000)
  centralHi := (548860999807593254323/100000000000000000000)
  directionLo := (275562176869509780347/50000000000000000000)
  directionHi := (110224870747803912139/20000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree123.table
  base := (19380790989584199275442931160749754032601/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-5179764358489569728569873026961905936000000000000)
      constant := (173920604583069686304177657471599950091547733791236) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree123.table
  base := (15504632791462835754311165588784917827957/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-5185105194695114565123860835572802936000000000000)
      constant := (174270215985275188717529411400684522540770509662065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275562176869509780347/50000000000000000000)
  centralHi := (110224870747803912139/20000000000000000000)
  directionLo := (276689225241385685271/50000000000000000000)
  directionHi := (553378450482771370543/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree124.table
  base := (79633995066002385431267068311895075236049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-15665555653939696970466919157236211568000000000000)
      constant := (530421747039429167112242741433314889763777310590123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree124.table
  base := (15926799013027194020409949835656140710557/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-15681708426854027695654589602791119568000000000000)
      constant := (531487699812857106595917658033731907676959559737195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276689225241385685271/50000000000000000000)
  centralHi := (553378450482771370543/100000000000000000000)
  directionLo := (555623402704722407353/100000000000000000000)
  directionHi := (277811701352361203677/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree125.table
  base := (10221351998241116046258374004750039522699/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-15791818232410684755224219233586705328000000000000)
      constant := (539153303162710294549486663678953297370701156877384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree125.table
  base := (81770815985194903251135436955006117278939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-15808101269622711695937596698863830328000000000000)
      constant := (540236513074871544565156818154740597700415957596153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555623402704722407353/100000000000000000000)
  centralHi := (277811701352361203677/50000000000000000000)
  directionLo := (278929660401881252249/50000000000000000000)
  directionHi := (557859320803762504499/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree126.table
  base := (83933626718063636846219550895334839215371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-5306026936960557513327173103312399696000000000000)
      constant := (182652160706347767051332214739434879038425160980739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree126.table
  base := (20983406679360452890783999763615661236837/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-5311498037463798565406867931645513696000000000000)
      constant := (183019029247286789062293673192280096501713025937332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278929660401881252249/50000000000000000000)
  centralHi := (557859320803762504499/100000000000000000000)
  directionLo := (560086312975148760437/100000000000000000000)
  directionHi := (280043156487574380219/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree127.table
  base := (86122427262377980107717417699700211111213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-16044343389352660324738819386287692848000000000000)
      constant := (556831283908423247019301397695051968860376674704351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree127.table
  base := (86122427261851236952598665760610471214301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-16060886955160079696503610891009251848000000000000)
      constant := (557949423813819166566021727995307975802034683689327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560086312975148760437/100000000000000000000)
  centralHi := (280043156487574380219/50000000000000000000)
  directionLo := (562304485271598533771/100000000000000000000)
  directionHi := (140576121317899633443/25000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree128.table
  base := (88337217618863381326690883233872129075133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-16170605967823648109496119462638186608000000000000)
      constant := (565777708530848647125746139119773432837429053074191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree128.table
  base := (88337217618417208724961324848940187859771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-16187279797928763696786617987081962608000000000000)
      constant := (566913521290746908917255027947655949160026974421017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562304485271598533771/100000000000000000000)
  centralHi := (140576121317899633443/25000000000000000000)
  directionLo := (282256970831110942673/50000000000000000000)
  directionHi := (564513941662221885347/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree129.table
  base := (90577997787527615030511712711110291109021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-5432289515431545298084473179662893456000000000000)
      constant := (191598585328773615860029471916726385449175101583589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree129.table
  base := (45288998893574855831690357919542592856047/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-5437890880232482565689875027718224456000000000000)
      constant := (191983126724215107679385857520370654908028749362446) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282256970831110942673/50000000000000000000)
  centralHi := (564513941662221885347/100000000000000000000)
  directionLo := (566714784089386127369/100000000000000000000)
  directionHi := (56671478408938612737/10000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree130.table
  base := (18568953553678358750147928103194580210251/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-16423131124765623679010719615339174128000000000000)
      constant := (583885426274843503874172619340874405772565983099885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree130.table
  base := (92844767768071732662604939322663538998827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-16440065483466131697352632179227384128000000000000)
      constant := (585057000459518388953864757324229385017497255994729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (566714784089386127369/100000000000000000000)
  centralHi := (56671478408938612737/10000000000000000000)
  directionLo := (568907112523600479383/100000000000000000000)
  directionHi := (71113389065450059923/12500000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree131.table
  base := (4756876378074392464016794814749027536411/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-16549393703236611463768019691689667888000000000000)
      constant := (593046719396422144781675953078745825703321210765940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree131.table
  base := (95137527561216792906891555031552453660047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-16566458326234815697635639275300094888000000000000)
      constant := (594236382151371910630391797728130684244468498551669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (568907112523600479383/100000000000000000000)
  centralHi := (71113389065450059923/12500000000000000000)
  directionLo := (71386378127063054887/12500000000000000000)
  directionHi := (571091025016504439097/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree132.table
  base := (24364069291714107263698728559766705853039/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-5558552093902533082841773256013387216000000000000)
      constant := (200759878450354602710249732546716930296739946955804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree132.table
  base := (97456277166626887473147126823623130737113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-5564283723001166565972882123790935216000000000000)
      constant := (201162508416071053076957469805549750501222211161217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71386378127063054887/12500000000000000000)
  centralHi := (571091025016504439097/100000000000000000000)
  directionLo := (573266617752039335293/100000000000000000000)
  directionHi := (286633308876019667647/50000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree133.table
  base := (24950254146136285220678969084824814493647/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-16801918860178587033282619844390655408000000000000)
      constant := (611584174138776736891003613744583020188425650315476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree133.table
  base := (99801016584350766745311286634155110666767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-16819244011772183698201653467445516408000000000000)
      constant := (612810429750050575554099389236251641573386160037109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (573266617752039335293/100000000000000000000)
  centralHi := (286633308876019667647/50000000000000000000)
  directionLo := (575433985095878624041/100000000000000000000)
  directionHi := (287716992547939312021/50000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree134.table
  base := (102171745814607089931478168810552138420421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-16928181438649574818039919920741149168000000000000)
      constant := (620960335759570125862489643454565162529862374638567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree134.table
  base := (20434349162888500906358910087257291526627/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-16945636854540867698484660563518227168000000000000)
      constant := (622205095656893522113757113663262024202999776026645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (575433985095878624041/100000000000000000000)
  centralHi := (287716992547939312021/50000000000000000000)
  directionLo := (288796609821594401667/50000000000000000000)
  directionHi := (115518643928637760667/20000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree135.table
  base := (52284232428549830424075864982132557180979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-5684814672373520867599073332363880976000000000000)
      constant := (210136040071151303602727077328010269954717818052822) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree135.table
  base := (52284232428480153301994490374391767566757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-5690676565769850566255889219863645976000000000000)
      constant := (210557174322917358948311476228121785209161496603226) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (288796609821594401667/50000000000000000000)
  centralHi := (115518643928637760667/20000000000000000000)
  directionLo := (144936103066197335271/25000000000000000000)
  directionHi := (115948882452957868217/20000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree136.table
  base := (26747793428020876359219192904429698311011/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-17180706595591550387554520073442136688000000000000)
      constant := (639927527500438593177170587567487460928819576689988) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree136.table
  base := (106991173711965520788925828626116399775877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-17198422540078235699050674755663648688000000000000)
      constant := (641209711685636861708372962936979734222817420535079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (144936103066197335271/25000000000000000000)
  centralHi := (115948882452957868217/20000000000000000000)
  directionLo := (72735956518972090533/12500000000000000000)
  directionHi := (116377530430355344853/20000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree137.table
  base := (54719936189810851325261265649660616557331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-17306969174062538172311820149792630448000000000000)
      constant := (649518557620535094662913270899633191067091839694274) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree137.table
  base := (109439872379521815978576205414994861659407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-17324815382846919699333681851736359448000000000000)
      constant := (650819661807558900541488109030450812342128302886389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72735956518972090533/12500000000000000000)
  centralHi := (116377530430355344853/20000000000000000000)
  directionLo := (584023026858674630731/100000000000000000000)
  directionHi := (146005756714668657683/25000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree138.table
  base := (13989320107472382872347859842994871630011/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-5811077250844508652356373408714374736000000000000)
      constant := (219727070191251545587579442942827963377255612227992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree138.table
  base := (13989320107461812831444958933605898981397/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-5817069408538534566538896315936356736000000000000)
      constant := (220167124444843167137101657383230807117000238794984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (584023026858674630731/100000000000000000000)
  centralHi := (146005756714668657683/25000000000000000000)
  directionLo := (117230124469033857763/20000000000000000000)
  directionHi := (36634413896573080551/6250000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree139.table
  base := (114415239152621553788589080012481163602289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-17559494331004513741826420302493617968000000000000)
      constant := (668915486360108641279432933847010558414815262046603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree139.table
  base := (57207619576274985949670403953225394984529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-17577601068384287699899696043881780968000000000000)
      constant := (670254846266560159485643782025812950513941932270166) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117230124469033857763/20000000000000000000)
  centralHi := (36634413896573080551/6250000000000000000)
  directionLo := (588270523016486312591/100000000000000000000)
  directionHi := (36766907688530394537/6250000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree140.table
  base := (58470953629107912965810160727088129818429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-17685756909475501526583720378844111728000000000000)
      constant := (678721384979608648356539118648463348140315442260766) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree140.table
  base := (29235476814538808410528578941988583323021/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-17703993911152971700182703139954491728000000000000)
      constant := (680080080603662477078328061665203998374824957315068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (588270523016486312591/100000000000000000000)
  centralHi := (36766907688530394537/6250000000000000000)
  directionLo := (295191405881231336591/50000000000000000000)
  directionHi := (590382811762462673183/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree141.table
  base := (59747282588314412545947633940002719913699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-5937339829315496437113673485064868496000000000000)
      constant := (229532968810755416395273865728814474252423337577782) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree141.table
  base := (119494565176577537821889417326777239926311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-5943462251307218566821903412009067496000000000000)
      constant := (229992358781949366020444283558681893102998242915199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295191405881231336591/50000000000000000000)
  centralHi := (590382811762462673183/100000000000000000000)
  directionLo := (592487569995364979391/100000000000000000000)
  directionHi := (9257618281177577803/1562500000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree142.table
  base := (24414642581585494799967964396520132755713/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 343470000000000000000000000000000000000000000
      center := (5289438)
      previous := (2644719)
      next := (2644719)
      square := (23557656090414188029269482158680000000000000)
      linear := (-3558476902681507061316865806694128000000000000)
      constant := (138573309009738748459588566026094240998802372055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree142.table
  base := (122073212907884064966210392679945104770863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 343470000000000000000000000000000000000000000
      center := (5289438)
      previous := (2644719)
      next := (2644719)
      square := (23557656090414188029269482158680000000000000)
      linear := (-3562146319518020174717063545348128000000000000)
      constant := (138850591845492690793094371771420130513564831461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (592487569995364979391/100000000000000000000)
  centralHi := (9257618281177577803/1562500000000000000)
  directionLo := (594584877686502885951/100000000000000000000)
  directionHi := (9290388713851607593/1562500000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree143.table
  base := (24935570090435682773688974027513628793761/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-18064544644888464880855620607895593008000000000000)
      constant := (708568817837100532228100647490419080203159485033735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree143.table
  base := (31169462613035418676207391868991393815009/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-18083172439459023701031724428172624008000000000000)
      constant := (709986352045515722050347036809791076015433997176172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (594584877686502885951/100000000000000000000)
  centralHi := (9290388713851607593/1562500000000000000)
  directionLo := (149168703350421054221/25000000000000000000)
  directionHi := (119334962680336843377/20000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree144.table
  base := (3182711945236194881997132197548862811561/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-6063602407786484221870973561415362256000000000000)
      constant := (239553735929766735480343780759115977735652859297960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree144.table
  base := (127308477809416702660142282327253205033811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-6069855094075902567104910508081778256000000000000)
      constant := (240032877334340262304044786516543295225882226882699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149168703350421054221/25000000000000000000)
  centralHi := (119334962680336843377/20000000000000000000)
  directionLo := (299378727167778138721/50000000000000000000)
  directionHi := (598757454335556277443/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree145.table
  base := (32491273744950277581047091026624121165519/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-18317069801830440450370220760596580528000000000000)
      constant := (728825220574703393135388345004542439578547843159252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree145.table
  base := (25993018995954959535261826901451460160641/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-18335958124996391701597738620318045528000000000000)
      constant := (730282673365655215526077482237417721290376605642535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299378727167778138721/50000000000000000000)
  centralHi := (598757454335556277443/100000000000000000000)
  directionLo := (120166575268975164797/20000000000000000000)
  directionHi := (300416438172437911993/50000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree146.table
  base := (16580962745412882389131347611501835258647/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-18443332380301428235127520836947074288000000000000)
      constant := (739060856193321294697298079663057550152836169870952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree146.table
  base := (26529540392656158529757675319184632716263/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-18462350967765075701880745716390756288000000000000)
      constant := (740538476133430233268911800368627387754517756003505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120166575268975164797/20000000000000000000)
  centralHi := (300416438172437911993/50000000000000000000)
  directionLo := (301450576990374130287/50000000000000000000)
  directionHi := (24116046159229930423/4000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree147.table
  base := (135356298760017444901907537768827934699239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-6189864986257472006628273637765856016000000000000)
      constant := (249789371548388319409433222452284428985857171634751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree147.table
  base := (16919537344999825413127571638771857308723/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-6196247936844586567387917604154489016000000000000)
      constant := (250288680102118968905314141911473604605242227917656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301450576990374130287/50000000000000000000)
  centralHi := (24116046159229930423/4000000000000000000)
  directionLo := (604962360519874827889/100000000000000000000)
  directionHi := (60496236051987482789/10000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree148.table
  base := (138090885370007092985636145990396330963669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-18695857537243403804642120989648061808000000000000)
      constant := (759746995930245261502685426954082544616009670419863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree148.table
  base := (27618177073998230040294041871269479459677/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-18715136653302443702446759908536177808000000000000)
      constant := (761265365884446130135360255031630926965293460788395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (604962360519874827889/100000000000000000000)
  centralHi := (60496236051987482789/10000000000000000000)
  directionLo := (24280662719793793553/4000000000000000000)
  directionHi := (303508283997422419413/50000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree149.table
  base := (70425730896666894658112423988672621360771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-18822120115714391589399421065998555568000000000000)
      constant := (770197500048572902339565869813510691369906044296034) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree149.table
  base := (1100402045260314843516000524094971647329/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-18841529496071127702729767004608888568000000000000)
      constant := (771736452867708615315457942188496190924982270807424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24280662719793793553/4000000000000000000)
  centralHi := (303508283997422419413/50000000000000000000)
  directionLo := (152265961805877097589/25000000000000000000)
  directionHi := (609063847223508390357/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree150.table
  base := (8977376751878639715512656104979285876381/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-6316127564728459791385573714116349776000000000000)
      constant := (260239875666719463600658679390883789465558023581264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree150.table
  base := (143638028030046822491566610277556685722239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-6322640779613270567670924700227199776000000000000)
      constant := (260759767085384961383167920867006611480457762041751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152265961805877097589/25000000000000000000)
  centralHi := (609063847223508390357/100000000000000000000)
  directionLo := (611104267837463438261/100000000000000000000)
  directionHi := (305552133918731719131/50000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree151.table
  base := (14645058408024001696966942391117275757967/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-19074645272656367158914021218699543088000000000000)
      constant := (791313376785012043730922315762088103609832773395090) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree151.table
  base := (146450584080230361215023329376217661125457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-19094315181608495703295781196754310088000000000000)
      constant := (792893911049795263496726551678827852259654076829739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (611104267837463438261/100000000000000000000)
  centralHi := (305552133918731719131/50000000000000000000)
  directionLo := (76642237288711206899/12500000000000000000)
  directionHi := (613137898309689655193/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree152.table
  base := (37322282485984395760057948591896091400409/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-19200907851127354943671321295050036848000000000000)
      constant := (801978749403143981202514352505762149831015053519372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree152.table
  base := (149289129943929414295720002828040556217887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-19220708024377179703578788292827020848000000000000)
      constant := (803580282248639881916508806501228919766439870301349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76642237288711206899/12500000000000000000)
  centralHi := (613137898309689655193/100000000000000000000)
  directionLo := (307582402990680049649/50000000000000000000)
  directionHi := (615164805981360099299/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree153.table
  base := (152153665621208235046185470702160735400357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-6442390143199447576142873790466843536000000000000)
      constant := (270905248284854708187895662489021345834636982644013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree153.table
  base := (76076832810600662303209609000928523261771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-6449033622381954567953931796299910536000000000000)
      constant := (271446138284232889312962030616710664160591731116678) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307582402990680049649/50000000000000000000)
  centralHi := (615164805981360099299/100000000000000000000)
  directionLo := (61718505708786039587/10000000000000000000)
  directionHi := (617185057087860395871/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree154.table
  base := (7752209555605406135490869722912925749019/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-19453433008069330513185921447751024368000000000000)
      constant := (823524363139282195758552135524770897075930834886260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree154.table
  base := (155044191112102276995600240068183587304773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-19473493709914547704144802484972442368000000000000)
      constant := (825168308861981349589832613739748994726384629722471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61718505708786039587/10000000000000000000)
  centralHi := (617185057087860395871/100000000000000000000)
  directionLo := (309599358392021937321/50000000000000000000)
  directionHi := (619198716784043874643/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree155.table
  base := (78980353208346123131845807825149829367277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-19579695586540318297943221524101518128000000000000)
      constant := (834404604257307717704861686782569142270299415965758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree155.table
  base := (157960706416687301435223354716553548738779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-19599886552683231704427809581045153128000000000000)
      constant := (836069964276497454936275295550207654336933976099833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (309599358392021937321/50000000000000000000)
  centralHi := (619198716784043874643/100000000000000000000)
  directionLo := (155301462292187476689/25000000000000000000)
  directionHi := (621205849168749906757/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree156.table
  base := (4022580288375361588266628364476721520397/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-6568652721670435360900173866817337296000000000000)
      constant := (281785489402883338506621432210692201888291772014920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree156.table
  base := (160903211535010280925494608733991780359343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-6575426465150638568236938892372621296000000000000)
      constant := (282347793698752104484916751295708811830297288873287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155301462292187476689/25000000000000000000)
  centralHi := (621205849168749906757/100000000000000000000)
  directionLo := (623206517308611544731/100000000000000000000)
  directionHi := (155801629327152886183/25000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree157.table
  base := (163871706467127500943195945310004182050121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-19832220743482293867457821676802505648000000000000)
      constant := (856379954993318218428223939707730082279653425680467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree157.table
  base := (5120990827097623850402252505174804911113/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-19852672238220599704993823773190574648000000000000)
      constant := (858088559321267058060296218203451020250977695412832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623206517308611544731/100000000000000000000)
  centralHi := (155801629327152886183/25000000000000000000)
  directionLo := (312600391630588741399/50000000000000000000)
  directionHi := (625200783261177482799/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree158.table
  base := (6674647648523318707887786882805726282739/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-19958483321953281652215121753152999408000000000000)
      constant := (867475064611321262212663456691783231510803621468825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree158.table
  base := (166866191213079975535793051469145517769041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-19979065080989283705276830869263285408000000000000)
      constant := (869205498951538627659577318021032974623117599435307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312600391630588741399/50000000000000000000)
  centralHi := (625200783261177482799/100000000000000000000)
  directionLo := (627188708097372320857/100000000000000000000)
  directionHi := (313594354048686160429/50000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree159.table
  base := (84943332886465686185608479912754036387387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-6694915300141423145657473943167831056000000000000)
      constant := (292880599020889297363821718317573152488925071518566) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree159.table
  base := (169886665772928841745220304978969517902699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-6701819307919322568519945988445332056000000000000)
      constant := (293464733329026590038396572176711827148769192289891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (627188708097372320857/100000000000000000000)
  centralHi := (313594354048686160429/50000000000000000000)
  directionLo := (125834070384663626029/20000000000000000000)
  directionHi := (314585175961659065073/50000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree160.table
  base := (86466565073361070727692492012178861769799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-20211008478895257221729721905853986928000000000000)
      constant := (889880152347366665926628071571910459336019860002746) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree160.table
  base := (172933130146720001258214560459001084077531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-20231850766526651705842845061408706928000000000000)
      constant := (891654662427899045527344305605628981373682035532537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125834070384663626029/20000000000000000000)
  centralHi := (314585175961659065073/50000000000000000000)
  directionLo := (315572886950769690003/50000000000000000000)
  directionHi := (631145773901539380007/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree161.table
  base := (88002792167251819664791233126837031031053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-20337271057366245006487021982204480688000000000000)
      constant := (901190130465425957682957127989695853599631307256062) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree161.table
  base := (88002792167250914697895436620464583149423/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-20358243609295335706125852157481417688000000000000)
      constant := (902986886274004829755228792843225654569401842816042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315572886950769690003/50000000000000000000)
  centralHi := (631145773901539380007/100000000000000000000)
  directionLo := (633115032271572390323/100000000000000000000)
  directionHi := (158278758067893097581/25000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree162.table
  base := (17910402833632318931014544274436628357071/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-6821177878612410930414774019518324816000000000000)
      constant := (304190577138951320357385029111828058487809937360390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree162.table
  base := (44776007084080414683552365317937308136697/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-6828212150688006568802953084518042816000000000000)
      constant := (304796957175135106037946365323330537104641434268292) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (633115032271572390323/100000000000000000000)
  centralHi := (158278758067893097581/25000000000000000000)
  directionLo := (317539092184999810507/50000000000000000000)
  directionHi := (127015636873999924203/20000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree163.table
  base := (1138927888451419346568469268620413915249/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-20589796214308220576001622134905468208000000000000)
      constant := (924024955201658693327534117168066850521906618963680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree163.table
  base := (182228462152225801164021755506932591142171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-20611029294832703706691866349626839208000000000000)
      constant := (925866618182108529193353760551024847235827102725817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (317539092184999810507/50000000000000000000)
  centralHi := (127015636873999924203/20000000000000000000)
  directionLo := (31851764332496414813/5000000000000000000)
  directionHi := (637035286649928296261/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree164.table
  base := (46344721445565166210154078512227961143747/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-20716058792779208360758922211255961968000000000000)
      constant := (935549801819847999064621249491999341280235865806276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree164.table
  base := (9268944289112978520284325036038365128259/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-20737422137601387706974873445699549968000000000000)
      constant := (937414126244122308757560389576914983754220643035860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31851764332496414813/5000000000000000000)
  centralHi := (637035286649928296261/100000000000000000000)
  directionLo := (638986394699932084767/100000000000000000000)
  directionHi := (19968324834372877649/3125000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree165.table
  base := (188555299226468230184030302641897628632207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-6947440457083398715172074095868818576000000000000)
      constant := (315715423757143184730334903674603267315009305370663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree165.table
  base := (23569412403308413097013368410451370651981/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-6954604993456690569085960180590753576000000000000)
      constant := (316344465237151444561909120154524893533352224753832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (638986394699932084767/100000000000000000000)
  centralHi := (19968324834372877649/3125000000000000000)
  directionLo := (64093156326247381647/10000000000000000000)
  directionHi := (640931563262473816471/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree166.table
  base := (11984856405305823280975809534424125941811/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-20968583949721183930273522363956949488000000000000)
      constant := (958814363556410869835511004866264031363513132225552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree166.table
  base := (191757702484892390038461877180882442481559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-20990207823138755707540887637844971488000000000000)
      constant := (960724426584112115928897305301888826726899013250893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64093156326247381647/10000000000000000000)
  centralHi := (640931563262473816471/100000000000000000000)
  directionLo := (160717711562956627207/25000000000000000000)
  directionHi := (642870846251826508829/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree167.table
  base := (194986095557577943763912788341303353203661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-21094846528192171715030822440307443248000000000000)
      constant := (970554078674799296272429989608760663255602653754047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree167.table
  base := (9749304777878864109971126306502159549061/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-21116600665907439707823894733917682248000000000000)
      constant := (972487218862103006457070815372056358981865727196940) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160717711562956627207/25000000000000000000)
  centralHi := (642870846251826508829/100000000000000000000)
  directionLo := (161201074192877325117/25000000000000000000)
  directionHi := (644804296771509300469/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree168.table
  base := (9912023922228204473723958171854275800263/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-7073703035554386499929374172219312336000000000000)
      constant := (327455138875534008940398987390277170246703621791340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree168.table
  base := (198240478444563530144282290173162699469299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8888018986)
      previous := (4444009493)
      next := (4444009493)
      square := (39584714783925973951849153187301960000000000000)
      linear := (-7080997836225374569368967276663464336000000000000)
      constant := (328107257515144733059441947368863405468715205429291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell201.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161201074192877325117/25000000000000000000)
  centralHi := (644804296771509300469/100000000000000000000)
  directionLo := (161682991782813561221/25000000000000000000)
  directionHi := (129346393426250848977/20000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree169.table
  base := (100760425572946135450199243690439097514863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-21347371685134147284545422593008430768000000000000)
      constant := (994248377411826101705848031750551157293382120565802) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree169.table
  base := (201520851145891798022531155629572116205861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (26664056958)
      previous := (13332028479)
      next := (13332028479)
      square := (118754144351777921855547459561905880000000000000)
      linear := (-21369386351444807708389908926063103768000000000000)
      constant := (996228087634112734814728292141005246491101769853447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell201.Kernel169
