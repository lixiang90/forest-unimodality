import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell014.Parameters
import ForestUnimodality.BinomialMassData.Q91_255.Batch000_049
import ForestUnimodality.BinomialMassData.Q91_255.Batch050_099
import ForestUnimodality.BinomialMassData.Q31_85.Batch000_049
import ForestUnimodality.BinomialMassData.Q31_85.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree000.table
  base := (862618755904846955639087009/100000000000000000000000000)
  polynomial :=
    { denominator := 106250000000000000000000000000000000000000
      center := (164)
      previous := (91)
      next := (0)
      square := (4126824066689422157439004437500000000000)
      linear := (9341810284339325740066151168750000000000)
      constant := (916532428148899890366529947062500000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree000.table
  base := (862618755904846955639087009/100000000000000000000000000)
  polynomial :=
    { denominator := 106250000000000000000000000000000000000000
      center := (162)
      previous := (93)
      next := (0)
      square := (4126824066689422157439004437500000000000)
      linear := (9341810284339325740066151168750000000000)
      constant := (916532428148899890366529947062500000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree001.table
  base := (11672988176995099869149832122525759323337/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (200736)
      previous := (111384)
      next := (0)
      square := (5051232657627852720705341431500000000000000)
      linear := (7829182283371455509102254753950000000000000)
      constant := (755598833102248224070762278150787499999988425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree001.table
  base := (14439913279352013949001146910216022683583/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3612500000000000000000000000000000000000000
      center := (5508)
      previous := (3162)
      next := (0)
      square := (140312018267440353352926150875000000000000)
      linear := (215276312813639405657761829687500000000000)
      constant := (20768499196093563268627714108484652777777435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (23953691065216395133/50000000000000000000)
  directionHi := (47907382130432790267/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree002.table
  base := (39483151255193824754827308904623606305267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (200736)
      previous := (111384)
      next := (0)
      square := (5051232657627852720705341431500000000000000)
      linear := (4223988778711576312363540477350000000000000)
      constant := (507890495110761946220228719499849999999997335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree002.table
  base := (38673159421437318039469757854877201076509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (451724303838966944613098078550000000000000)
      constant := (55254615063061835477585271467797555555555505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23953691065216395133/50000000000000000000)
  centralHi := (47907382130432790267/100000000000000000000)
  directionLo := (67751269546648511997/100000000000000000000)
  directionHi := (33875634773324255999/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree003.table
  base := (6655863298974732835600841774244024209203/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3612500000000000000000000000000000000000000
      center := (5576)
      previous := (3094)
      next := (0)
      square := (140312018267440353352926150875000000000000)
      linear := (17188757612547142100689616687500000000000)
      constant := (9438500479003855631143643264755114982298335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree003.table
  base := (6451622248163927863328594314896565335919/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3612500000000000000000000000000000000000000
      center := (5508)
      previous := (3162)
      next := (0)
      square := (140312018267440353352926150875000000000000)
      linear := (10585839105844066648787209587500000000000)
      constant := (9143045400620849608460251840983036910402955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67751269546648511997/100000000000000000000)
  centralHi := (33875634773324255999/50000000000000000000)
  directionLo := (3319120796301076621/4000000000000000000)
  directionHi := (41489009953763457763/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree004.table
  base := (177906658559635094999509974631375977139/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32512500000000000000000000000000000000000000
      center := (50184)
      previous := (27846)
      next := (0)
      square := (1262808164406963180176335357875000000000000)
      linear := (-746599557652045520278472018962500000000000)
      constant := (56334518133367033028676142527756114567317375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree004.table
  base := (17053721146668556512784018892389783546191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-367037590992214411422800401850000000000000)
      constant := (23983641013688630030007917161383237224245995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3319120796301076621/4000000000000000000)
  centralHi := (41489009953763457763/50000000000000000000)
  directionLo := (23953691065216395133/25000000000000000000)
  directionHi := (95814764260865580533/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree005.table
  base := (2329770702693034985804115457851808192629/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (200736)
      previous := (111384)
      next := (0)
      square := (5051232657627852720705341431500000000000000)
      linear := (-6591591735268061277852602352450000000000000)
      constant := (147172816915149326599491613845763827725700725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree005.table
  base := (11020931831131363385506199134603677249747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-776418538407805089440749642050000000000000)
      constant := (15474773041039742458307762031152313625884415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23953691065216395133/25000000000000000000)
  centralHi := (95814764260865580533/100000000000000000000)
  directionLo := (21424832613541283087/20000000000000000000)
  directionHi := (26781040766926603859/25000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree006.table
  base := (7318566093012948117331809956685674971473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22304)
      previous := (12376)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-1132976137769771163843479625450000000000000)
      constant := (10428111350969188624258559023310800333778485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree006.table
  base := (3400123087605490324987544912023505230857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (11016)
      previous := (6324)
      next := (0)
      square := (280624036534880706705852301750000000000000)
      linear := (-592899742911697883729349441125000000000000)
      constant := (4866849248091415957332310139443965058588365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21424832613541283087/20000000000000000000)
  centralHi := (26781040766926603859/25000000000000000000)
  directionLo := (117348641132089238203/100000000000000000000)
  directionHi := (29337160283022309551/25000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree007.table
  base := (4213865601418510719122254021245270433093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (200736)
      previous := (111384)
      next := (0)
      square := (5051232657627852720705341431500000000000000)
      linear := (-13801978744587819671330030905650000000000000)
      constant := (57758504662774165084570271221664741982374465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree007.table
  base := (237086535075288223999689363319023819157/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1806250000000000000000000000000000000000000
      center := (2754)
      previous := (1581)
      next := (0)
      square := (70156009133720176676463075437500000000000)
      linear := (-199397554154873305684581015306250000000000)
      constant := (736987916442169641938220193285728837363730) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117348641132089238203/100000000000000000000)
  centralHi := (29337160283022309551/25000000000000000000)
  directionLo := (25350203816252978789/20000000000000000000)
  directionHi := (63375509540632446973/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree008.table
  base := (1943785023258316745252979018853864501601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (200736)
      previous := (111384)
      next := (0)
      square := (5051232657627852720705341431500000000000000)
      linear := (-17407172249247698868068745182250000000000000)
      constant := (33804798391720513409469543195954507843321005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree008.table
  base := (321083235470943653655101383456476953037/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-2004561380654577123494597362650000000000000)
      constant := (3390712524113675827456395726753045985692325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25350203816252978789/20000000000000000000)
  centralHi := (63375509540632446973/50000000000000000000)
  directionLo := (27100507818659404799/20000000000000000000)
  directionHi := (33875634773324255999/25000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree009.table
  base := (246822674182929564820620839139522241193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22304)
      previous := (12376)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-2334707305989730896089717717650000000000000)
      constant := (2065672660066368800902955208586609638523885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree009.table
  base := (-2505371105111953108821013613721312089/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (11016)
      previous := (6324)
      next := (0)
      square := (280624036534880706705852301750000000000000)
      linear := (-1206971164035083900756273301425000000000000)
      constant := (920205341126170376262093065605863520156975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27100507818659404799/20000000000000000000)
  centralHi := (33875634773324255999/25000000000000000000)
  directionLo := (71861073195649185399/50000000000000000000)
  directionHi := (143722146391298370799/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree010.table
  base := (-1052487550117661149718940531181645078513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (200736)
      previous := (111384)
      next := (0)
      square := (5051232657627852720705341431500000000000000)
      linear := (-24617559258567457261546173735450000000000000)
      constant := (9835334622852898170830151492882705753938435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree010.table
  base := (-635823955322121777427098726555609568867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (11016)
      previous := (6324)
      next := (0)
      square := (280624036534880706705852301750000000000000)
      linear := (-1411661637742879239765247921525000000000000)
      constant := (497056425185531547656856393277144172987185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71861073195649185399/50000000000000000000)
  centralHi := (143722146391298370799/100000000000000000000)
  directionLo := (15149644426821743179/10000000000000000000)
  directionHi := (151496444268217431791/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree011.table
  base := (-2072361918568026117502974182187079969673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (200736)
      previous := (111384)
      next := (0)
      square := (5051232657627852720705341431500000000000000)
      linear := (-28222752763227336458284888012050000000000000)
      constant := (6000237861123208095200022526307024994402635) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree011.table
  base := (-562553012892847816503188118024250695733/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3612500000000000000000000000000000000000000
      center := (5508)
      previous := (3162)
      next := (0)
      square := (140312018267440353352926150875000000000000)
      linear := (-808176055725337289387111270812500000000000)
      constant := (171105523226951805450998973552457744665815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15149644426821743179/10000000000000000000)
  centralHi := (151496444268217431791/100000000000000000000)
  directionLo := (31778162242964536401/20000000000000000000)
  directionHi := (79445405607411341003/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree012.table
  base := (-723213290845745885878136787623992331991/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3612500000000000000000000000000000000000000
      center := (5576)
      previous := (3094)
      next := (0)
      square := (140312018267440353352926150875000000000000)
      linear := (-884109618552422657083988952462500000000000)
      constant := (167907718693181617373817587953331080273005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree012.table
  base := (-759620627914972381259980554933242327403/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3612500000000000000000000000000000000000000
      center := (5508)
      previous := (3162)
      next := (0)
      square := (140312018267440353352926150875000000000000)
      linear := (-910521292579234958891598580862500000000000)
      constant := (199752335975521454651786875171464836902665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31778162242964536401/20000000000000000000)
  centralHi := (79445405607411341003/50000000000000000000)
  directionLo := (165956039815053831051/100000000000000000000)
  directionHi := (41489009953763457763/25000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree013.table
  base := (-356851423332972593632611330815099886189/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (100368)
      previous := (55692)
      next := (0)
      square := (2525616328813926360352670715750000000000000)
      linear := (-17716569886273547425881158282625000000000000)
      constant := (4629596779814774993769795403503129900560275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree013.table
  base := (-28820258439650680317775332619055544343/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 1806250000000000000000000000000000000000000
      center := (2754)
      previous := (1581)
      next := (0)
      square := (70156009133720176676463075437500000000000)
      linear := (-506433264716566314198042945456250000000000)
      constant := (157745409715085117974317282563685814789840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165956039815053831051/100000000000000000000)
  centralHi := (41489009953763457763/25000000000000000000)
  directionLo := (34546504548904535123/20000000000000000000)
  directionHi := (5397891335766333613/3125000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree014.table
  base := (-2068404424840447423061520770675238671251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (100368)
      previous := (55692)
      next := (0)
      square := (2525616328813926360352670715750000000000000)
      linear := (-19519166638603487024250515420925000000000000)
      constant := (7578284612998770010681901541678521080380745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree014.table
  base := (-847510813491526892648341188702352103311/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-4460847065148121191602292803850000000000000)
      constant := (2021537996355719581049444148605506053578025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34546504548904535123/20000000000000000000)
  centralHi := (5397891335766333613/3125000000000000000)
  directionLo := (179253010229335770781/100000000000000000000)
  directionHi := (89626505114667885391/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree015.table
  base := (-4623704553039902581586694023959219510881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22304)
      previous := (12376)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-4738169642429650360582193902050000000000000)
      constant := (2599899667390125694722549436028927806776955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree015.table
  base := (-47088309235613848617060011121584213533/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3612500000000000000000000000000000000000000
      center := (5508)
      previous := (3162)
      next := (0)
      square := (140312018267440353352926150875000000000000)
      linear := (-1217557003140927967405060511012500000000000)
      constant := (760522981011254218078749966720270286120375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179253010229335770781/100000000000000000000)
  centralHi := (89626505114667885391/50000000000000000000)
  directionLo := (185544493151560996451/100000000000000000000)
  directionHi := (46386123287890249113/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree016.table
  base := (-5047398365982097434740496023118701897759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (200736)
      previous := (111384)
      next := (0)
      square := (5051232657627852720705341431500000000000000)
      linear := (-46248720286526732441978459395050000000000000)
      constant := (33750124622577919143192370730541281819644205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree016.table
  base := (-2560010815833368488874213623500041845893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (11016)
      previous := (6324)
      next := (0)
      square := (280624036534880706705852301750000000000000)
      linear := (-2639804479989651273819095642125000000000000)
      constant := (2149386987618842846831586560362439532684615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185544493151560996451/100000000000000000000)
  centralHi := (46386123287890249113/25000000000000000000)
  directionLo := (23953691065216395133/12500000000000000000)
  directionHi := (38325905704346232213/20000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree017.table
  base := (-8673286296665135156145442736475056063/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7650000000000000000000000000000000000000000
      center := (11808)
      previous := (6552)
      next := (0)
      square := (297131332801638395335608319500000000000000)
      linear := (-2932583164187447743453951392450000000000000)
      constant := (2708335888009198333647832000132863819878125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree017.table
  base := (-1096657374298882552809060147683403150191/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (1296)
      previous := (744)
      next := (0)
      square := (33014592533515377259512035500000000000000)
      linear := (-334646465140876072097420030850000000000000)
      constant := (339647762808075460204510983884553661168825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23953691065216395133/12500000000000000000)
  centralHi := (38325905704346232213/20000000000000000000)
  directionLo := (197527196770602421217/100000000000000000000)
  directionHi := (98763598385301210609/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree018.table
  base := (-1150643296921557823991691126478504998647/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22304)
      previous := (12376)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-5939900810649610092828431994250000000000000)
      constant := (6683663227628722007130453656332801384775425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree018.table
  base := (-2903680555804804442717481381155042287873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (11016)
      previous := (6324)
      next := (0)
      square := (280624036534880706705852301750000000000000)
      linear := (-3049185427405241951837044882325000000000000)
      constant := (3727592297233549540532068841820963894023515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (197527196770602421217/100000000000000000000)
  centralHi := (98763598385301210609/50000000000000000000)
  directionLo := (203253808639945535993/100000000000000000000)
  directionHi := (101626904319972767997/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree019.table
  base := (-6051431297999123990267129376232453745841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (200736)
      previous := (111384)
      next := (0)
      square := (5051232657627852720705341431500000000000000)
      linear := (-57064300800506370032194602224850000000000000)
      constant := (75995528805931855407096436958066939035337795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree019.table
  base := (-6098625052469319429637530470664862362403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-6507751802226074581692039004850000000000000)
      constant := (9333071743266778009669956708919273886327665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203253808639945535993/100000000000000000000)
  centralHi := (101626904319972767997/50000000000000000000)
  directionLo := (104411718678071416049/50000000000000000000)
  directionHi := (208823437356142832099/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree020.table
  base := (-3160249215593014053616403639380884824457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (100368)
      previous := (55692)
      next := (0)
      square := (2525616328813926360352670715750000000000000)
      linear := (-30334747152583124614466658250725000000000000)
      constant := (46751856697473189911177565176751592857936715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree020.table
  base := (-6361823189828458869771050021450862800027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-6917132749641665259709988245050000000000000)
      constant := (11400817617770468195638567103603503253960985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104411718678071416049/50000000000000000000)
  centralHi := (208823437356142832099/100000000000000000000)
  directionLo := (21424832613541283087/10000000000000000000)
  directionHi := (214248326135412830871/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree021.table
  base := (-6564234775463213229506827993410179653759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22304)
      previous := (12376)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-7141631978869569825074670086450000000000000)
      constant := (12514209349379371654298833767272290400318245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree021.table
  base := (-6600547020760440235320937641855896894179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-7326513697057255937727937485250000000000000)
      constant := (13653232504707087811363542419408228987911345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21424832613541283087/10000000000000000000)
  centralHi := (214248326135412830871/100000000000000000000)
  directionLo := (8781568198395321393/4000000000000000000)
  directionHi := (109769602479941517413/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree022.table
  base := (-678557385708316713547895858171735492593/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (100368)
      previous := (55692)
      next := (0)
      square := (2525616328813926360352670715750000000000000)
      linear := (-33939940657243003811205372527325000000000000)
      constant := (66664945272711073524070318489292899594140175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree022.table
  base := (-6817563014742764485729258032911556734881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-7735894644472846615745886725450000000000000)
      constant := (16086318855681647970451099163342800518096955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8781568198395321393/4000000000000000000)
  centralHi := (109769602479941517413/50000000000000000000)
  directionLo := (112352770078232653641/50000000000000000000)
  directionHi := (224705540156465307283/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree023.table
  base := (-3493403384941306451012527235995627824563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (100368)
      previous := (55692)
      next := (0)
      square := (2525616328813926360352670715750000000000000)
      linear := (-35742537409572943409574729665625000000000000)
      constant := (77789968461311601342969014863881860141558185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree023.table
  base := (-1403007472414188555042194616386238274671/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-8145275591888437293763835965650000000000000)
      constant := (18696946525717135055060617408239428465502025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112352770078232653641/50000000000000000000)
  centralHi := (224705540156465307283/100000000000000000000)
  directionLo := (229755733420518047769/100000000000000000000)
  directionHi := (22975573342051804777/10000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree024.table
  base := (-3584874883212712567361041020877531105379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (11152)
      previous := (6188)
      next := (0)
      square := (280624036534880706705852301750000000000000)
      linear := (-4171681573544764778660454089325000000000000)
      constant := (9964133495079129030919624134071967552727345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree024.table
  base := (-179867293733976588112362680171083852763/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1806250000000000000000000000000000000000000
      center := (2754)
      previous := (1581)
      next := (0)
      square := (70156009133720176676463075437500000000000)
      linear := (-1069332067413003496472723150731250000000000)
      constant := (2685328459707023912154940483773919163787325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229755733420518047769/100000000000000000000)
  centralHi := (22975573342051804777/10000000000000000000)
  directionLo := (234697282264178476407/100000000000000000000)
  directionHi := (29337160283022309551/12500000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree025.table
  base := (-183396554642004287354815220958576340267/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16256250000000000000000000000000000000000000
      center := (25092)
      previous := (13923)
      next := (0)
      square := (631404082203481590088167678937500000000000)
      linear := (-9836932728558205651578360985556250000000000)
      constant := (25579288726067410529198720010262323474138325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree025.table
  base := (-1839478191382073878999860392296978244719/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3612500000000000000000000000000000000000000
      center := (5508)
      previous := (3162)
      next := (0)
      square := (140312018267440353352926150875000000000000)
      linear := (-2241009371679904662449933611512500000000000)
      constant := (6110339672626931951597880942693366436381045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234697282264178476407/100000000000000000000)
  centralHi := (29337160283022309551/12500000000000000000)
  directionLo := (23953691065216395133/10000000000000000000)
  directionHi := (239536910652163951331/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree026.table
  base := (-7486330536426596615302879426457967980461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (200736)
      previous := (111384)
      next := (0)
      square := (5051232657627852720705341431500000000000000)
      linear := (-82300655333125524409365602161050000000000000)
      constant := (231404227067287508740612096170214126414104695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree026.table
  base := (-7505829898244529195688432133497430235179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-9373418434135209327817683686250000000000000)
      constant := (27571507454594532888100579241236213310166345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23953691065216395133/10000000000000000000)
  centralHi := (239536910652163951331/100000000000000000000)
  directionLo := (9771227053128923123/4000000000000000000)
  directionHi := (61070169082055769519/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree027.table
  base := (-1524425867417132716166053204108246128007/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22304)
      previous := (12376)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-9545094315309489289567146270850000000000000)
      constant := (28850164563956041242900057447647921725149425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree027.table
  base := (-7639372058180515831542256687478250000459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-9782799381550800005835632926450000000000000)
      constant := (30871731693994480960134466378343928749336745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9771227053128923123/4000000000000000000)
  centralHi := (61070169082055769519/25000000000000000000)
  directionLo := (248934059722580746577/100000000000000000000)
  directionHi := (124467029861290373289/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree028.table
  base := (-3872032921417135165567823187240205715389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (100368)
      previous := (55692)
      next := (0)
      square := (2525616328813926360352670715750000000000000)
      linear := (-44755521171222641401421515357125000000000000)
      constant := (144682786739957156927830903734321124671366055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree028.table
  base := (-3879654631371191884641525014630188251707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (11016)
      previous := (6324)
      next := (0)
      square := (280624036534880706705852301750000000000000)
      linear := (-5096090164483195341926791083325000000000000)
      constant := (17170459366777858281462350199399377976283385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248934059722580746577/100000000000000000000)
  centralHi := (124467029861290373289/50000000000000000000)
  directionLo := (25350203816252978789/10000000000000000000)
  directionHi := (253502038162529787891/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree029.table
  base := (-392640673989879921572583231947573735773/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32512500000000000000000000000000000000000000
      center := (50184)
      previous := (27846)
      next := (0)
      square := (1262808164406963180176335357875000000000000)
      linear := (-23279058961776290499895436247712500000000000)
      constant := (80134436593364837623361357577526517831360675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree029.table
  base := (-3933141965295695865975422185374491485451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (11016)
      previous := (6324)
      next := (0)
      square := (280624036534880706705852301750000000000000)
      linear := (-5300780638190990680935765703425000000000000)
      constant := (18989070139156360420839217378198859803523305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25350203816252978789/10000000000000000000)
  centralHi := (253502038162529787891/100000000000000000000)
  directionLo := (128994574125375540921/50000000000000000000)
  directionHi := (257989148250751081843/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree030.table
  base := (-3974468631730580013272921151188675627263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (11152)
      previous := (6188)
      next := (0)
      square := (280624036534880706705852301750000000000000)
      linear := (-5373412741764724510906692181525000000000000)
      constant := (19620036207213910869819431588682363718604965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree030.table
  base := (-7960834796379321497399394869310670047963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-11010942223797572039889480647050000000000000)
      constant := (41782617856693669127396993248746081780693465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128994574125375540921/50000000000000000000)
  centralHi := (257989148250751081843/100000000000000000000)
  directionLo := (262399538638579414379/100000000000000000000)
  directionHi := (13119976931928970719/5000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree031.table
  base := (-4016456722918272754650049698752883614439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (100368)
      previous := (55692)
      next := (0)
      square := (2525616328813926360352670715750000000000000)
      linear := (-50163311428212460196529586772025000000000000)
      constant := (193614047945838358143072726150643748594220805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree031.table
  base := (-8043415498234579495344824324757065764613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-11420323171213162717907429887250000000000000)
      constant := (45753695961603014129140578430116039970134215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262399538638579414379/100000000000000000000)
  centralHi := (13119976931928970719/5000000000000000000)
  directionLo := (266737014942303502679/100000000000000000000)
  directionHi := (6668425373557587567/2500000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree032.table
  base := (-1013143117783030933764328237433043582849/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16256250000000000000000000000000000000000000
      center := (25092)
      previous := (13923)
      next := (0)
      square := (631404082203481590088167678937500000000000)
      linear := (-12991477045135599948724735977581250000000000)
      constant := (52841854868116900780434751349823268205048755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree032.table
  base := (-507150578296416844757941425412373995081/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1806250000000000000000000000000000000000000
      center := (2754)
      previous := (1581)
      next := (0)
      square := (70156009133720176676463075437500000000000)
      linear := (-1478713014828594174490672390931250000000000)
      constant := (6236352605634337858733498918758239154215910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266737014942303502679/100000000000000000000)
  centralHi := (6668425373557587567/2500000000000000000)
  directionLo := (27100507818659404799/10000000000000000000)
  directionHi := (271005078186594047991/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree033.table
  base := (-2041493405175147719249156692271081697713/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3612500000000000000000000000000000000000000
      center := (5576)
      previous := (3094)
      next := (0)
      square := (140312018267440353352926150875000000000000)
      linear := (-2987139162937352188514905613812500000000000)
      constant := (12768789858245940536661492877015786946804715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree033.table
  base := (-1021767575588058307975777482945653447539/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1806250000000000000000000000000000000000000
      center := (2754)
      previous := (1581)
      next := (0)
      square := (70156009133720176676463075437500000000000)
      linear := (-1529885633255543009242916045956250000000000)
      constant := (6774190442483933889151546713834780768306145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27100507818659404799/10000000000000000000)
  centralHi := (271005078186594047991/100000000000000000000)
  directionLo := (13760347893995382569/5000000000000000000)
  directionHi := (275206957879907651381/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree034.table
  base := (-8215690218774829288813613230765328912867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7650000000000000000000000000000000000000000
      center := (11808)
      previous := (6552)
      next := (0)
      square := (297131332801638395335608319500000000000000)
      linear := (-6537776668847326940192665669050000000000000)
      constant := (29297006041444954881298862773524523381656745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree034.table
  base := (-8222884950493936607290032469213684782657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (1296)
      previous := (744)
      next := (0)
      square := (33014592533515377259512035500000000000000)
      linear := (-744027412556466750115369271050000000000000)
      constant := (3450670946954878682388355622656836793474155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13760347893995382569/5000000000000000000)
  centralHi := (275206957879907651381/100000000000000000000)
  directionLo := (139672820305262483057/50000000000000000000)
  directionHi := (55869128122104993223/20000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree035.table
  base := (-66036339495694636909704852630290962313/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (200736)
      previous := (111384)
      next := (0)
      square := (5051232657627852720705341431500000000000000)
      linear := (-114747396875064437180014030650450000000000000)
      constant := (537849621023390683089820267098533254389929375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree035.table
  base := (-8260876337532149973840339118942258922903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-13057846960875525429979226848050000000000000)
      constant := (63294130321635656142643650347678435856405165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139672820305262483057/50000000000000000000)
  centralHi := (55869128122104993223/20000000000000000000)
  directionLo := (5668477897661624867/2000000000000000000)
  directionHi := (283423894883081243351/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree036.table
  base := (-2070685401694829435261828946580786652631/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3612500000000000000000000000000000000000000
      center := (5576)
      previous := (3094)
      next := (0)
      square := (140312018267440353352926150875000000000000)
      linear := (-3287571954992342121576465136862500000000000)
      constant := (16085423374637366234777974047840763286948205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree036.table
  base := (-4144156953722218467680810027438334629033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (11016)
      previous := (6324)
      next := (0)
      square := (280624036534880706705852301750000000000000)
      linear := (-6733613954145558053998588044125000000000000)
      constant := (34045704225215512175967607024171606461047315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5668477897661624867/2000000000000000000)
  centralHi := (283423894883081243351/100000000000000000000)
  directionLo := (71861073195649185399/25000000000000000000)
  directionHi := (287444292782596741597/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree037.table
  base := (-830046822895716307732927444848430251171/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (100368)
      previous := (55692)
      next := (0)
      square := (2525616328813926360352670715750000000000000)
      linear := (-60978891942192097786745729601825000000000000)
      constant := (310861808341617892718469530558365822917605725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree037.table
  base := (-4152683628289842430015981572944389823079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (11016)
      previous := (6324)
      next := (0)
      square := (280624036534880706705852301750000000000000)
      linear := (-6938304427853353393007562664225000000000000)
      constant := (36526497708947449990729699858320356705650845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71861073195649185399/25000000000000000000)
  centralHi := (287444292782596741597/100000000000000000000)
  directionLo := (291409228947675073913/100000000000000000000)
  directionHi := (145704614473837536957/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree038.table
  base := (-4153938301679109457517297830923552253539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (100368)
      previous := (55692)
      next := (0)
      square := (2525616328813926360352670715750000000000000)
      linear := (-62781488694522037385115086740125000000000000)
      constant := (332896369971273039487985452480469202942725305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree038.table
  base := (-25975565379200005931423155049777994793/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1806250000000000000000000000000000000000000
      center := (2754)
      previous := (1581)
      next := (0)
      square := (70156009133720176676463075437500000000000)
      linear := (-1785748725390287183004134321081250000000000)
      constant := (9772335296115057094271420972995331900964600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291409228947675073913/100000000000000000000)
  centralHi := (145704614473837536957/50000000000000000000)
  directionLo := (295320937250425607713/100000000000000000000)
  directionHi := (147660468625212803857/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree039.table
  base := (-8305098720247973402241295130577293564037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22304)
      previous := (12376)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-14352018988189328218552098639650000000000000)
      constant := (79031210525719265744816444780245810799966535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree039.table
  base := (-1038609768544760913461388424142733209371/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1806250000000000000000000000000000000000000
      center := (2754)
      previous := (1581)
      next := (0)
      square := (70156009133720176676463075437500000000000)
      linear := (-1836921343817236017756377976106250000000000)
      constant := (10433536401517598030235831186767500512458905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295320937250425607713/100000000000000000000)
  centralHi := (147660468625212803857/50000000000000000000)
  directionLo := (74795376378264991293/25000000000000000000)
  directionHi := (299181505513059965173/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree040.table
  base := (-2073061886185427001949102571528402109369/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32512500000000000000000000000000000000000000
      center := (50184)
      previous := (27846)
      next := (0)
      square := (1262808164406963180176335357875000000000000)
      linear := (-33193341099590958290926900508362500000000000)
      constant := (189546652984673372029178658376173130567656155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree040.table
  base := (-8295564074885005745094435612652268675523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-15104751697953478820068973049050000000000000)
      constant := (88921670024210754016460721996917471763869265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74795376378264991293/25000000000000000000)
  centralHi := (299181505513059965173/100000000000000000000)
  directionLo := (302992888536434863581/100000000000000000000)
  directionHi := (151496444268217431791/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree041.table
  base := (-2067354949620581669777665889751446635583/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32512500000000000000000000000000000000000000
      center := (50184)
      previous := (27846)
      next := (0)
      square := (1262808164406963180176335357875000000000000)
      linear := (-34094639475755928090111579077512500000000000)
      constant := (201627158424810100594998587799769936504243085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree041.table
  base := (-4136164209673505953015104374527308382851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (11016)
      previous := (6324)
      next := (0)
      square := (280624036534880706705852301750000000000000)
      linear := (-7757066322684534749043461144625000000000000)
      constant := (47269344581005104021256714188253039386780305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (302992888536434863581/100000000000000000000)
  centralHi := (151496444268217431791/50000000000000000000)
  directionLo := (958615373972911069/312500000000000000)
  directionHi := (306756919671331542081/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree042.table
  base := (-8236698321831567260999840829821951093317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22304)
      previous := (12376)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-15553750156409287950798336731850000000000000)
      constant := (95138431408245525980150873414287280670156935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree042.table
  base := (-4119623881201565260900730796344385316771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (11016)
      previous := (6324)
      next := (0)
      square := (280624036534880706705852301750000000000000)
      linear := (-7961756796392330088052435764725000000000000)
      constant := (50159618983243427791655941680432363217265905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (958615373972911069/312500000000000000)
  centralHi := (306756919671331542081/100000000000000000000)
  directionLo := (310475321126873244171/100000000000000000000)
  directionHi := (77618830281718311043/25000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree043.table
  base := (-4097077042030139015748050717453678028157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (100368)
      previous := (55692)
      next := (0)
      square := (2525616328813926360352670715750000000000000)
      linear := (-71794472456171735376961872431625000000000000)
      constant := (453698717954117050292498464962019917243818215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree043.table
  base := (-8196387484195140378958983953360594815983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-16332894540200250854122820769650000000000000)
      constant := (106263221963335826292290195674823940490904565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310475321126873244171/100000000000000000000)
  centralHi := (77618830281718311043/25000000000000000000)
  directionLo := (314149713180557232339/100000000000000000000)
  directionHi := (15707485659027861617/5000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree044.table
  base := (-4070923948404122934973739570363470804693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (100368)
      previous := (55692)
      next := (0)
      square := (2525616328813926360352670715750000000000000)
      linear := (-73597069208501674975331229569925000000000000)
      constant := (479981251272969037152495189826283062184967535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree044.table
  base := (-2035950852939598795640043259245743849393/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3612500000000000000000000000000000000000000
      center := (5508)
      previous := (3162)
      next := (0)
      square := (140312018267440353352926150875000000000000)
      linear := (-4185568871903960383035192502462500000000000)
      constant := (28092640120622758516410106588959900137627115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314149713180557232339/100000000000000000000)
  centralHi := (15707485659027861617/5000000000000000000)
  directionLo := (317781622429645364011/100000000000000000000)
  directionHi := (79445405607411341003/25000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree045.table
  base := (-201995796912226341116676605631752267187/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1806250000000000000000000000000000000000000
      center := (2788)
      previous := (1547)
      next := (0)
      square := (70156009133720176676463075437500000000000)
      linear := (-2094435165578655960380571853006250000000000)
      constant := (14082505622407819580262867650679339869573925) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree045.table
  base := (-8081543221384739451299988041180223453101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-17151656435031432210158719250050000000000000)
      constant := (118641184631710763573848359363344577110269055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (317781622429645364011/100000000000000000000)
  centralHi := (79445405607411341003/25000000000000000000)
  directionLo := (160686244601559623153/50000000000000000000)
  directionHi := (321372489203119246307/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree046.table
  base := (-8008150693669076587533906998131938108489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (200736)
      previous := (111384)
      next := (0)
      square := (5051232657627852720705341431500000000000000)
      linear := (-154404525426323108344139887693050000000000000)
      constant := (1069330561769793197116218154236794144899100555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree046.table
  base := (-8009647633321480719651446799294033129401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-17561037382447022888176668490250000000000000)
      constant := (125075035570237655429600483928160122128015555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160686244601559623153/50000000000000000000)
  centralHi := (321372489203119246307/100000000000000000000)
  directionLo := (162461837118136999397/50000000000000000000)
  directionHi := (64984734847254799759/20000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree047.table
  base := (-1585368528255457764804839693942778583577/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (200736)
      previous := (111384)
      next := (0)
      square := (5051232657627852720705341431500000000000000)
      linear := (-158009718930982987540878601969650000000000000)
      constant := (1126132475415687327815047565725940822602905575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree047.table
  base := (-7928151430169021767589108100639513549653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-17970418329862613566194617730450000000000000)
      constant := (131672063037214127615833562599725902920751415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (162461837118136999397/50000000000000000000)
  centralHi := (64984734847254799759/20000000000000000000)
  directionLo := (164218232347836166361/50000000000000000000)
  directionHi := (328436464695672332723/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree048.table
  base := (-1567188109692760884764113813911048084899/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22304)
      previous := (12376)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-17957212492849207415290812916250000000000000)
      constant := (131593968756438685377688010731132677586604725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree048.table
  base := (-489817770337120687086038733440870083571/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1806250000000000000000000000000000000000000
      center := (2754)
      previous := (1581)
      next := (0)
      square := (70156009133720176676463075437500000000000)
      linear := (-2297474909659775530526570871331250000000000)
      constant := (17304028012085123599632078040215885458479810) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (164218232347836166361/50000000000000000000)
  centralHi := (328436464695672332723/100000000000000000000)
  directionLo := (331912079630107662103/100000000000000000000)
  directionHi := (41489009953763457763/12500000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree049.table
  base := (-1933868140693106329002847448350412623773/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32512500000000000000000000000000000000000000
      center := (50184)
      previous := (27846)
      next := (0)
      square := (1262808164406963180176335357875000000000000)
      linear := (-41305026485075686483589007630712500000000000)
      constant := (310992481471942143695214370499970383827832135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree049.table
  base := (-1934117926069649303931982916333218219951/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3612500000000000000000000000000000000000000
      center := (5508)
      previous := (3162)
      next := (0)
      square := (140312018267440353352926150875000000000000)
      linear := (-4697295056173448730557629052712500000000000)
      constant := (36338870516726296782557002849480999672170805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331912079630107662103/100000000000000000000)
  centralHi := (41489009953763457763/12500000000000000000)
  directionLo := (167675837456514765931/50000000000000000000)
  directionHi := (335351674913029531863/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree050.table
  base := (-3812731409921386614473583621440819689953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (100368)
      previous := (55692)
      next := (0)
      square := (2525616328813926360352670715750000000000000)
      linear := (-84412649722481312565547372399725000000000000)
      constant := (652502391385577633191422691815412139932161235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree050.table
  base := (-953291907026808038657052824877015056737/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1806250000000000000000000000000000000000000
      center := (2754)
      previous := (1581)
      next := (0)
      square := (70156009133720176676463075437500000000000)
      linear := (-2399820146513673200031058181381250000000000)
      constant := (19055225700839510777066423949490213243015035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167675837456514765931/50000000000000000000)
  centralHi := (335351674913029531863/100000000000000000000)
  directionLo := (84689086933310639997/25000000000000000000)
  directionHi := (338756347733242559989/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree051.table
  base := (-7505932016973082323121701406158770138323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (1312)
      previous := (728)
      next := (0)
      square := (33014592533515377259512035500000000000000)
      linear := (-1126996685945245126325708882850000000000000)
      constant := (8937581831959115738221790409326504538242545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree051.table
  base := (-7506693514384581787527246232047438403767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (1296)
      previous := (744)
      next := (0)
      square := (33014592533515377259512035500000000000000)
      linear := (-1153408359972057428133318511250000000000000)
      constant := (9393598113862598794639124577945967735679805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84689086933310639997/25000000000000000000)
  centralHi := (338756347733242559989/100000000000000000000)
  directionLo := (342127140683338454643/100000000000000000000)
  directionHi := (85531785170834613661/25000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree052.table
  base := (-3688448952225015621781006126076463292443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (100368)
      previous := (55692)
      next := (0)
      square := (2525616328813926360352670715750000000000000)
      linear := (-88017843227141191762286086676325000000000000)
      constant := (715652703800529321848773367146235594881778785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree052.table
  base := (-7377562316473137977398073230095708017751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-20017323066940566956284363931450000000000000)
      constant := (167103546168295814874919855973511701914349805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342127140683338454643/100000000000000000000)
  centralHi := (85531785170834613661/25000000000000000000)
  directionLo := (345465045489045351231/100000000000000000000)
  directionHi := (5397891335766333613/1562500000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree053.table
  base := (-11309962041414284590413182841428525433/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 16256250000000000000000000000000000000000000
      center := (25092)
      previous := (13923)
      next := (0)
      square := (631404082203481590088167678937500000000000)
      linear := (-22455109994867782840163860953656250000000000)
      constant := (187071343339245766012774177856466512139506800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree053.table
  base := (-1809738799501554773319398622252892653491/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3612500000000000000000000000000000000000000
      center := (5508)
      previous := (3162)
      next := (0)
      square := (140312018267440353352926150875000000000000)
      linear := (-5106676003589039408575578292912500000000000)
      constant := (43669730186443949433718761924177070115705505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345465045489045351231/100000000000000000000)
  centralHi := (5397891335766333613/1562500000000000000)
  directionLo := (348771006417304540273/100000000000000000000)
  directionHi := (174385503208652270137/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree054.table
  base := (-7090378482023555751235723461167337615821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22304)
      previous := (12376)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-20360674829289126879783289100650000000000000)
      constant := (173693985310851767307828915970993197145138655) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree054.table
  base := (-1772720932051623122835441833143546880437/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3612500000000000000000000000000000000000000
      center := (5508)
      previous := (3162)
      next := (0)
      square := (140312018267440353352926150875000000000000)
      linear := (-5209021240442937078080065602962500000000000)
      constant := (45604318737644343439764108665452574757768535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (348771006417304540273/100000000000000000000)
  centralHi := (174385503208652270137/50000000000000000000)
  directionLo := (352045923396267714611/100000000000000000000)
  directionHi := (88011480849066928653/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree055.table
  base := (-3466458716829295266541724794938657956047/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (100368)
      previous := (55692)
      next := (0)
      square := (2525616328813926360352670715750000000000000)
      linear := (-93425633484131010557394158091225000000000000)
      constant := (815665312580825785133900822468547753281608765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree055.table
  base := (-6933357796784053222708579071874390163621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-21245465909187338990338211652050000000000000)
      constant := (190318594492069455598598525204291506213567655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352045923396267714611/100000000000000000000)
  centralHi := (88011480849066928653/25000000000000000000)
  directionLo := (177645327438214728633/50000000000000000000)
  directionHi := (355290654876429457267/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree056.table
  base := (-3383001086376204217583302527411269021909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (100368)
      previous := (55692)
      next := (0)
      square := (2525616328813926360352670715750000000000000)
      linear := (-95228230236460950155763515229525000000000000)
      constant := (850412446905209152705795983022816446370073455) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree056.table
  base := (-105724779044449326118350833731708992101/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1806250000000000000000000000000000000000000
      center := (2754)
      previous := (1581)
      next := (0)
      square := (70156009133720176676463075437500000000000)
      linear := (-2706855857075366208544520111531250000000000)
      constant := (24797858394078010241792185893391444051312440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (177645327438214728633/50000000000000000000)
  centralHi := (355290654876429457267/100000000000000000000)
  directionLo := (179253010229335770781/50000000000000000000)
  directionHi := (358506020458671541563/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree057.table
  base := (-6589640946394931522030687575440964502807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22304)
      previous := (12376)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-21562405997509086612029527192850000000000000)
      constant := (196858729610062408305824112135917806293443885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree057.table
  base := (-411873446502606682753814384107194025011/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1806250000000000000000000000000000000000000
      center := (2754)
      previous := (1581)
      next := (0)
      square := (70156009133720176676463075437500000000000)
      linear := (-2758028475502315043296763766556250000000000)
      constant := (25826260310674064778603443844911459267718210) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179253010229335770781/50000000000000000000)
  centralHi := (358506020458671541563/100000000000000000000)
  directionLo := (361692803312016050611/100000000000000000000)
  directionHi := (90423200828004012653/25000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree058.table
  base := (-640384083204143847242933623998042972359/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (100368)
      previous := (55692)
      next := (0)
      square := (2525616328813926360352670715750000000000000)
      linear := (-98833423741120829352502229506125000000000000)
      constant := (922020775579887889536542849063657255722356025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree058.table
  base := (-3202065917598337334951831268001000118037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (11016)
      previous := (6324)
      next := (0)
      square := (280624036534880706705852301750000000000000)
      linear := (-11236804375717055512196029686325000000000000)
      constant := (107500115778098652484200565403128554829436535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (361692803312016050611/100000000000000000000)
  centralHi := (90423200828004012653/25000000000000000000)
  directionLo := (72970350480259046097/20000000000000000000)
  directionHi := (182425876200647615243/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree059.table
  base := (-1552151976082582901831848451694756810449/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32512500000000000000000000000000000000000000
      center := (50184)
      previous := (27846)
      next := (0)
      square := (1262808164406963180176335357875000000000000)
      linear := (-50318010246725384475435793322212500000000000)
      constant := (479440942204347049047362563171402187680110755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree059.table
  base := (-310443061042613776173575779310951000053/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3612500000000000000000000000000000000000000
      center := (5508)
      previous := (3162)
      next := (0)
      square := (140312018267440353352926150875000000000000)
      linear := (-5720747424712425425602502153212500000000000)
      constant := (55888326680773590719823695945335879024617075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72970350480259046097/20000000000000000000)
  centralHi := (182425876200647615243/50000000000000000000)
  directionLo := (367983584542690370019/100000000000000000000)
  directionHi := (18399179227134518501/5000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree060.table
  base := (-3001973689038278559013876048984081083309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (11152)
      previous := (6188)
      next := (0)
      square := (280624036534880706705852301750000000000000)
      linear := (-11382068582864523172137882642525000000000000)
      constant := (110716397313596141715756475819518002834618495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree060.table
  base := (-750520978195336128351968722407205768133/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1806250000000000000000000000000000000000000
      center := (2754)
      previous := (1581)
      next := (0)
      square := (70156009133720176676463075437500000000000)
      linear := (-2911546330783161547553494731631250000000000)
      constant := (29033662681012862815405572848346587665047815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367983584542690370019/100000000000000000000)
  centralHi := (18399179227134518501/5000000000000000000)
  directionLo := (185544493151560996451/50000000000000000000)
  directionHi := (371088986303121992903/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree061.table
  base := (-5789863730846373927025760043354571083449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (200736)
      previous := (111384)
      next := (0)
      square := (5051232657627852720705341431500000000000000)
      linear := (-208482427996221296295220601842050000000000000)
      constant := (2069435641411053645868532621492323803059745755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree061.table
  base := (-723756940146713749529454557599284589787/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1806250000000000000000000000000000000000000
      center := (2754)
      previous := (1581)
      next := (0)
      square := (70156009133720176676463075437500000000000)
      linear := (-2962718949210110382305738386656250000000000)
      constant := (30143526267050718798837260091005283767757785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185544493151560996451/50000000000000000000)
  centralHi := (371088986303121992903/100000000000000000000)
  directionLo := (2923192310607413643/781250000000000000)
  directionHi := (74833723151549789261/20000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree062.table
  base := (-2783180404015737932357029968140189536127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (100368)
      previous := (55692)
      next := (0)
      square := (2525616328813926360352670715750000000000000)
      linear := (-106043810750440587745979658059325000000000000)
      constant := (1073692594053519251439971054941846835082668365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree062.table
  base := (-2783263810933839566224728466222920652819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (11016)
      previous := (6324)
      next := (0)
      square := (280624036534880706705852301750000000000000)
      linear := (-12055566270548236868231928166725000000000000)
      constant := (125095013999504712084558680562157879656676545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2923192310607413643/781250000000000000)
  centralHi := (74833723151549789261/20000000000000000000)
  directionLo := (47152888014790065077/12500000000000000000)
  directionHi := (377223104118320520617/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree063.table
  base := (-2666720956461450864056005715426838149831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (11152)
      previous := (6188)
      next := (0)
      square := (280624036534880706705852301750000000000000)
      linear := (-11982934166974503038261001688625000000000000)
      constant := (123707986042965842353478236534653218873494205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree063.table
  base := (-1066717393068652389374246709582742676327/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-24520513488512064414481805573650000000000000)
      constant := (259394750935439352194509161674494684163537425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47152888014790065077/12500000000000000000)
  centralHi := (377223104118320520617/100000000000000000000)
  directionLo := (76050611448758936367/20000000000000000000)
  directionHi := (95063264310948670459/25000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree064.table
  base := (-127277747098188479915808169034241088647/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16256250000000000000000000000000000000000000
      center := (25092)
      previous := (13923)
      next := (0)
      square := (631404082203481590088167678937500000000000)
      linear := (-27412251063775116735679593083981250000000000)
      constant := (288438910812076506255721092763188473210728825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree064.table
  base := (-5091235982153849724722042800813984432363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-24929894435927655092499754813850000000000000)
      constant := (268762375433545884059729026845303792495235465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76050611448758936367/20000000000000000000)
  centralHi := (95063264310948670459/25000000000000000000)
  directionLo := (23953691065216395133/6250000000000000000)
  directionHi := (383259057043462322129/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree065.table
  base := (-4839367160763673011748427671582634122403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (200736)
      previous := (111384)
      next := (0)
      square := (5051232657627852720705341431500000000000000)
      linear := (-222903202014860813082175458948450000000000000)
      constant := (2389687769548182872866561713551417843238148985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree065.table
  base := (-75616824295825131634575862444239373587/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1806250000000000000000000000000000000000000
      center := (2754)
      previous := (1581)
      next := (0)
      square := (70156009133720176676463075437500000000000)
      linear := (-3167409422917905721314713006756250000000000)
      constant := (34786612310490475744323013032075842841334280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23953691065216395133/6250000000000000000)
  centralHi := (383259057043462322129/100000000000000000000)
  directionLo := (96560415695445310549/25000000000000000000)
  directionHi := (386241662781781242197/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree066.table
  base := (-2289107920604776084504031000854753594809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (11152)
      previous := (6188)
      next := (0)
      square := (280624036534880706705852301750000000000000)
      linear := (-12583799751084482904384120734725000000000000)
      constant := (137404065035916194590993817294414881055500995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree066.table
  base := (-4578311068981464083135213289162937743967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-25748656330758836448535653294250000000000000)
      constant := (287986317506812701756199614917299554959967685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96560415695445310549/25000000000000000000)
  centralHi := (386241662781781242197/100000000000000000000)
  directionLo := (38920141229320652127/10000000000000000000)
  directionHi := (389201412293206521271/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree067.table
  base := (-4307657729754042419074947470784700165479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (200736)
      previous := (111384)
      next := (0)
      square := (5051232657627852720705341431500000000000000)
      linear := (-230113589024180571475652887501650000000000000)
      constant := (2558267466324160240272368086413614974347945605) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree067.table
  base := (-2153870227740125615564263915338585339613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (11016)
      previous := (6324)
      next := (0)
      square := (280624036534880706705852301750000000000000)
      linear := (-13079018639087213563276801267225000000000000)
      constant := (148921315144828421783756305145610744184259215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38920141229320652127/10000000000000000000)
  centralHi := (389201412293206521271/100000000000000000000)
  directionLo := (392138823114490717333/100000000000000000000)
  directionHi := (196069411557245358667/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree068.table
  base := (-805538875861138817115779670921568487673/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7650000000000000000000000000000000000000000
      center := (11808)
      previous := (6552)
      next := (0)
      square := (297131332801638395335608319500000000000000)
      linear := (-13748163678167085333670094222250000000000000)
      constant := (155568860963859611106540829661005000534650775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree068.table
  base := (-2013883114199731946486637988620796241821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 425000000000000000000000000000000000000000
      center := (648)
      previous := (372)
      next := (0)
      square := (16507296266757688629756017750000000000000)
      linear := (-781394653693824053075633875725000000000000)
      constant := (9054759850993210485979214731987232319445215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (392138823114490717333/100000000000000000000)
  centralHi := (196069411557245358667/50000000000000000000)
  directionLo := (79010878708240968487/20000000000000000000)
  directionHi := (98763598385301210609/25000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree069.table
  base := (-116822722717230533731404942984427221189/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1806250000000000000000000000000000000000000
      center := (2788)
      previous := (1547)
      next := (0)
      square := (70156009133720176676463075437500000000000)
      linear := (-3296166333798615692626809945206250000000000)
      constant := (37951148103361613959212594080028760661527580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree069.table
  base := (-3738389516028931665224822685260132627013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-26976799173005608482589501014850000000000000)
      constant := (318043929808770836856519184344329108353966215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79010878708240968487/20000000000000000000)
  centralHi := (98763598385301210609/25000000000000000000)
  directionLo := (198974301807293987399/50000000000000000000)
  directionHi := (397948603614587974799/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree070.table
  base := (-1719778562307033429933371959993771217909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (100368)
      previous := (55692)
      next := (0)
      square := (2525616328813926360352670715750000000000000)
      linear := (-120464584769080104532934515165725000000000000)
      constant := (1410851766256335196590166253039431005311093455) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree070.table
  base := (-429951410988970917418173688146780814201/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1806250000000000000000000000000000000000000
      center := (2754)
      previous := (1581)
      next := (0)
      square := (70156009133720176676463075437500000000000)
      linear := (-3423272515052649895075931281881250000000000)
      constant := (41048614189209010822940918815140401723479555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198974301807293987399/50000000000000000000)
  centralHi := (397948603614587974799/100000000000000000000)
  directionLo := (400821916044259950587/100000000000000000000)
  directionHi := (100205479011064987647/25000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree071.table
  base := (-3131385365338027148024903474832572306081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (200736)
      previous := (111384)
      next := (0)
      square := (5051232657627852720705341431500000000000000)
      linear := (-244534363042820088262607744608050000000000000)
      constant := (2912333230682975303469877575420052397159416595) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree071.table
  base := (-626286475570548977729205760432253992153/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-27795561067836789838625399495250000000000000)
      constant := (338896784843625007312883328750266964906694575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (400821916044259950587/100000000000000000000)
  centralHi := (100205479011064987647/25000000000000000000)
  directionLo := (403674777071819392401/100000000000000000000)
  directionHi := (201837388535909696201/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree072.table
  base := (-2813812705825633224786096943676435022217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22304)
      previous := (12376)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-27571061838608885273260717653850000000000000)
      constant := (333819082979059616155972318570867551392896435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree072.table
  base := (-175865843973375361737728106428338155139/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1806250000000000000000000000000000000000000
      center := (2754)
      previous := (1581)
      next := (0)
      square := (70156009133720176676463075437500000000000)
      linear := (-3525617751906547564580418591931250000000000)
      constant := (43695942845190138076709873167972102731648290) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (403674777071819392401/100000000000000000000)
  centralHi := (201837388535909696201/50000000000000000000)
  directionLo := (203253808639945535993/50000000000000000000)
  directionHi := (406507617279891071987/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree073.table
  base := (-1243419942880467328026102298217201448531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (100368)
      previous := (55692)
      next := (0)
      square := (2525616328813926360352670715750000000000000)
      linear := (-125872375026069923328042586580625000000000000)
      constant := (1548909535639381527188699214160940295161854345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree073.table
  base := (-2486875283507214724923698739717203742949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-28614322962667971194661297975650000000000000)
      constant := (360401186373726623011601950062238640591438695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203253808639945535993/50000000000000000000)
  centralHi := (406507617279891071987/100000000000000000000)
  directionLo := (409320852350775925501/100000000000000000000)
  directionHi := (204660426175387962751/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree074.table
  base := (-2150467544378644536890509455160094172489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (200736)
      previous := (111384)
      next := (0)
      square := (5051232657627852720705341431500000000000000)
      linear := (-255349943556799725852823887437850000000000000)
      constant := (3192675195771407386589470243270462975286780555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree074.table
  base := (-107524912556995358286816805101943818553/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3612500000000000000000000000000000000000000
      center := (5508)
      previous := (3162)
      next := (0)
      square := (140312018267440353352926150875000000000000)
      linear := (-7255925977520890468169811803962500000000000)
      constant := (92849428727338018439668035358033455910954575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409320852350775925501/100000000000000000000)
  centralHi := (204660426175387962751/50000000000000000000)
  directionLo := (412114883778488418393/100000000000000000000)
  directionHi := (206057441889244209197/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree075.table
  base := (-1804696234671744169120583514578999834711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22304)
      previous := (12376)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-28772793006828845005506955746050000000000000)
      constant := (365437790344199535578866975354683345238842605) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree075.table
  base := (-360944573454562023311427664723003924089/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-29433084857499152550697196456050000000000000)
      constant := (382557127702540406330763551362126296648456975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (412114883778488418393/100000000000000000000)
  centralHi := (206057441889244209197/50000000000000000000)
  directionLo := (414890099537634577629/100000000000000000000)
  directionHi := (41489009953763457763/10000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree076.table
  base := (-1449526435574748178495563220354544165719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (200736)
      previous := (111384)
      next := (0)
      square := (5051232657627852720705341431500000000000000)
      linear := (-262560330566119484246301315991050000000000000)
      constant := (3386613817029384992530476493611089153124824405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree076.table
  base := (-289909906098570629338688686693452211009/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-29842465804914743228715145696250000000000000)
      constant := (393879424177333507500227076400279807775459975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414890099537634577629/100000000000000000000)
  centralHi := (41489009953763457763/10000000000000000000)
  directionLo := (104411718678071416049/25000000000000000000)
  directionHi := (417646874712285664197/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree077.table
  base := (-1084958562411549131737791491892938450083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (200736)
      previous := (111384)
      next := (0)
      square := (5051232657627852720705341431500000000000000)
      linear := (-266165524070779363443040030267650000000000000)
      constant := (3485696302164887680721267319860402335456670585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree077.table
  base := (-216995717224424139352206419551111097923/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-30251846752330333906733094936450000000000000)
      constant := (405364603834740965250372913483993222317506325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104411718678071416049/25000000000000000000)
  centralHi := (417646874712285664197/100000000000000000000)
  directionLo := (420385572087733464871/100000000000000000000)
  directionHi := (52548196510966683109/12500000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree078.table
  base := (-710992975855507454285941254986112381661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22304)
      previous := (12376)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-29974524175048804737753193838250000000000000)
      constant := (398465284868194092494371701726685067608499855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree078.table
  base := (-711010333865019948848462302576893328107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-30661227699745924584751044176650000000000000)
      constant := (417012666241689911203083096323356389140885385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420385572087733464871/100000000000000000000)
  centralHi := (52548196510966683109/12500000000000000000)
  directionLo := (211553271353885154633/50000000000000000000)
  directionHi := (423106542707770309267/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree079.table
  base := (-327629989614090274869830781040603164923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (200736)
      previous := (111384)
      next := (0)
      square := (5051232657627852720705341431500000000000000)
      linear := (-273375911080099121836517458820850000000000000)
      constant := (3688087597896196837705579194030736955840176385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree079.table
  base := (-327645034343503994197399058791523513181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-31070608647161515262768993416850000000000000)
      constant := (428823611021581623141513418977676248523453455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211553271353885154633/50000000000000000000)
  centralHi := (423106542707770309267/100000000000000000000)
  directionLo := (212905063199958663937/50000000000000000000)
  directionHi := (3406481011199338623/800000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree080.table
  base := (65130122979949617257465350400321073187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (200736)
      previous := (111384)
      next := (0)
      square := (5051232657627852720705341431500000000000000)
      linear := (-276981104584759001033256173097450000000000000)
      constant := (3791396400857545246465732720425156175556796935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree080.table
  base := (65117085317511126471907494794749710817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-31479989594577105940786942657050000000000000)
      constant := (440797437846220597386823119996378413332130565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212905063199958663937/50000000000000000000)
  centralHi := (3406481011199338623/800000000000000000)
  directionLo := (428496652270825661741/100000000000000000000)
  directionHi := (214248326135412830871/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree081.table
  base := (467287123314847380537403386330787375361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22304)
      previous := (12376)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-31176255343268764469999431930450000000000000)
      constant := (432901552177182895218370781468397987757396645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree081.table
  base := (116818956679013873317627315097391162339/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3612500000000000000000000000000000000000000
      center := (5508)
      previous := (3162)
      next := (0)
      square := (140312018267440353352926150875000000000000)
      linear := (-7972342635498174154701222974312500000000000)
      constant := (113233536607228996851193167344538230229579855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (428496652270825661741/100000000000000000000)
  centralHi := (214248326135412830871/50000000000000000000)
  directionLo := (215583219586947556197/50000000000000000000)
  directionHi := (86233287834779022479/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree082.table
  base := (439420401324909204759647548139721653847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (100368)
      previous := (55692)
      next := (0)
      square := (2525616328813926360352670715750000000000000)
      linear := (-142095745797039379713366800825325000000000000)
      constant := (2001120150696412682705252965982367080108280235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree082.table
  base := (175766203218413277841373861302911702261/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-32298751489408287296822841137450000000000000)
      constant := (465233736518584502569309296257013537048835725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215583219586947556197/50000000000000000000)
  centralHi := (86233287834779022479/20000000000000000000)
  directionLo := (433819796150991137323/100000000000000000000)
  directionHi := (108454949037747784331/25000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree083.table
  base := (324947744488532072359734544356377216989/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32512500000000000000000000000000000000000000
      center := (50184)
      previous := (27846)
      next := (0)
      square := (1262808164406963180176335357875000000000000)
      linear := (-71949171274684659655868078981812500000000000)
      constant := (1027443848467942117684307741431107185706941945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree083.table
  base := (1299782500838384435501025615424846701873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-32708132436823877974840790377650000000000000)
      constant := (477696207894708797578095955517318903484206485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (433819796150991137323/100000000000000000000)
  centralHi := (108454949037747784331/25000000000000000000)
  directionLo := (436457022849992431921/100000000000000000000)
  directionHi := (218228511424996215961/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree084.table
  base := (216267186042120737274083716685332563533/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1806250000000000000000000000000000000000000
      center := (2788)
      previous := (1547)
      next := (0)
      square := (70156009133720176676463075437500000000000)
      linear := (-4047248313936090525280708752831250000000000)
      constant := (58593322846376255198646583312895305554305185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree084.table
  base := (1730130146517506516490350495463364746687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-33117513384239468652858739617850000000000000)
      constant := (490321560363026680429000150144624562058962715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (436457022849992431921/100000000000000000000)
  centralHi := (218228511424996215961/50000000000000000000)
  directionLo := (8781568198395321393/2000000000000000000)
  directionHi := (439078409919766069651/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree085.table
  base := (433976038396774916704693480830101400273/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7650000000000000000000000000000000000000000
      center := (11808)
      previous := (6552)
      next := (0)
      square := (297131332801638395335608319500000000000000)
      linear := (-17353357182826964530408808498850000000000000)
      constant := (254651285455911415726110144387125137856044225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree085.table
  base := (216987383431040501244171188270537702999/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 425000000000000000000000000000000000000000
      center := (648)
      previous := (372)
      next := (0)
      square := (16507296266757688629756017750000000000000)
      linear := (-986085127401619392084608495825000000000000)
      constant := (14797346875054254594456103067839978523774575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8781568198395321393/2000000000000000000)
  centralHi := (439078409919766069651/100000000000000000000)
  directionLo := (44168423938404394679/10000000000000000000)
  directionHi := (441684239384043946791/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree086.table
  base := (1309509481763761235542140011014670722863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (100368)
      previous := (55692)
      next := (0)
      square := (2525616328813926360352670715750000000000000)
      linear := (-149306132806359138106844229378525000000000000)
      constant := (2220416607837788699417651466725195792750833315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree086.table
  base := (2619013458834473626014800977228776349913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-33936275279070650008894638098250000000000000)
      constant := (516060907908884858825961271787235581825624285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44168423938404394679/10000000000000000000)
  centralHi := (441684239384043946791/100000000000000000000)
  directionLo := (444274784995561895261/100000000000000000000)
  directionHi := (222137392497780947631/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree087.table
  base := (307755369179090184121667223006038121329/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (11152)
      previous := (6188)
      next := (0)
      square := (280624036534880706705852301750000000000000)
      linear := (-16789858839854341967245954057425000000000000)
      constant := (253000185126026854632371526850983625426602025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree087.table
  base := (615509785255368386395813487730991579811/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-34345656226486240686912587338450000000000000)
      constant := (529174902698587690507903307344806414164134475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444274784995561895261/100000000000000000000)
  centralHi := (222137392497780947631/50000000000000000000)
  directionLo := (223425156285860109039/50000000000000000000)
  directionHi := (446850312571720218079/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree088.table
  base := (3545484277849884371026429897396824497611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (200736)
      previous := (111384)
      next := (0)
      square := (5051232657627852720705341431500000000000000)
      linear := (-305822652622038034607165887310250000000000000)
      constant := (4668582201242703732146786849411405702591431055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree088.table
  base := (1772740076398571334169959967724732022501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (11016)
      previous := (6324)
      next := (0)
      square := (280624036534880706705852301750000000000000)
      linear := (-17377518586950915682465268289325000000000000)
      constant := (271225888999901910281875713252602237772513945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223425156285860109039/50000000000000000000)
  centralHi := (446850312571720218079/100000000000000000000)
  directionLo := (112352770078232653641/25000000000000000000)
  directionHi := (89882216062586122913/20000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree089.table
  base := (201140531668481703935196661841044493343/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32512500000000000000000000000000000000000000
      center := (50184)
      previous := (27846)
      next := (0)
      square := (1262808164406963180176335357875000000000000)
      linear := (-77356961531674478450976150396712500000000000)
      constant := (1196142455362360975796041731599681418179628575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree089.table
  base := (804561412632102654955879923529693530119/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-35164418121317422042948485818850000000000000)
      constant := (555891533703818872593846178730232035755109775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112352770078232653641/25000000000000000000)
  centralHi := (89882216062586122913/20000000000000000000)
  directionLo := (451957339104728646783/100000000000000000000)
  directionHi := (3530916711755692553/781250000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree090.table
  base := (2254766339587936608686671383924032067387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (11152)
      previous := (6188)
      next := (0)
      square := (280624036534880706705852301750000000000000)
      linear := (-17390724423964321833369073103525000000000000)
      constant := (272331455103280134133150412324220226337374215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree090.table
  base := (4509529589567333287920931348172343038571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-35573799068733012720966435059050000000000000)
      constant := (569494169712662395028608412946809035690735095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451957339104728646783/100000000000000000000)
  centralHi := (3530916711755692553/781250000000000000)
  directionLo := (113622333201163073843/25000000000000000000)
  directionHi := (454489332804652295373/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree091.table
  base := (2502825172013781301963282242161177445217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (100368)
      previous := (55692)
      next := (0)
      square := (2525616328813926360352670715750000000000000)
      linear := (-158319116568008836098691015070025000000000000)
      constant := (2510385655772504775604043786586531112675047085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree091.table
  base := (5005647670651084565504525546737035500843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-35983180016148603398984384299250000000000000)
      constant := (583259685937659769152472444211425016298718135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113622333201163073843/25000000000000000000)
  centralHi := (454489332804652295373/100000000000000000000)
  directionLo := (457007298514815082721/100000000000000000000)
  directionHi := (228503649257407541361/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree092.table
  base := (5511163563562329335881239860231918897691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (200736)
      previous := (111384)
      next := (0)
      square := (5051232657627852720705341431500000000000000)
      linear := (-320243426640677551394120744416650000000000000)
      constant := (5140985179670312654021524307779236105264471455) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree092.table
  base := (2755580625309946879701637295668495454093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (11016)
      previous := (6324)
      next := (0)
      square := (280624036534880706705852301750000000000000)
      linear := (-18196280481782097038501166769725000000000000)
      constant := (298594041149095868988697445505140975931164385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457007298514815082721/100000000000000000000)
  centralHi := (228503649257407541361/50000000000000000000)
  directionLo := (459511466841036095539/100000000000000000000)
  directionHi := (22975573342051804777/5000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree093.table
  base := (241042891175602601641090545220009393671/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22304)
      previous := (12376)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-35983180016148603398984384299250000000000000)
      constant := (584734199497287595939602800742462839346364875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree093.table
  base := (1506517569630220009413592757068816136947/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3612500000000000000000000000000000000000000
      center := (5508)
      previous := (3162)
      next := (0)
      square := (140312018267440353352926150875000000000000)
      linear := (-9200485477744946188755070694912500000000000)
      constant := (152819839680157847175297374143196939317888415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (459511466841036095539/100000000000000000000)
  centralHi := (22975573342051804777/5000000000000000000)
  directionLo := (231001031069664235699/50000000000000000000)
  directionHi := (462002062139328471399/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree094.table
  base := (818797054789203001023007526592686498827/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16256250000000000000000000000000000000000000
      center := (25092)
      previous := (13923)
      next := (0)
      square := (631404082203481590088167678937500000000000)
      linear := (-40931726706249663723449771621231250000000000)
      constant := (673204894783625974942360860554115387917245135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree094.table
  base := (6550374707609474630779062780737195119471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-37211322858395375433038232019850000000000000)
      constant := (625533515137432819451959464147945246947635595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231001031069664235699/50000000000000000000)
  centralHi := (462002062139328471399/100000000000000000000)
  directionLo := (116119825687623008617/25000000000000000000)
  directionHi := (464479302750492034469/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree095.table
  base := (7084075991658556157634625065827486257201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (200736)
      previous := (111384)
      next := (0)
      square := (5051232657627852720705341431500000000000000)
      linear := (-331059007154657188984336887246450000000000000)
      constant := (5510079267417559738982189696974136458774899005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree095.table
  base := (1771018623702119560310054945896866016741/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3612500000000000000000000000000000000000000
      center := (5508)
      previous := (3162)
      next := (0)
      square := (140312018267440353352926150875000000000000)
      linear := (-9405175951452741527764045315012500000000000)
      constant := (159987637871587369311190910197908471394190745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116119825687623008617/25000000000000000000)
  centralHi := (464479302750492034469/100000000000000000000)
  directionLo := (116735850305876083363/25000000000000000000)
  directionHi := (466943401223504333453/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree096.table
  base := (3813585447348193156296163407403135631113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (11152)
      previous := (6188)
      next := (0)
      square := (280624036534880706705852301750000000000000)
      linear := (-18592455592184281565615311195725000000000000)
      constant := (313107117907752797895123527959697530986958285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree096.table
  base := (1525433920048768504856106798580353728729/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-38030084753226556789074130500250000000000000)
      constant := (654530467709763362221427716380383055690067025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116735850305876083363/25000000000000000000)
  centralHi := (466943401223504333453/100000000000000000000)
  directionLo := (234697282264178476407/50000000000000000000)
  directionHi := (93878912905671390563/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree097.table
  base := (817966110614815990579750159525263891113/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (100368)
      previous := (55692)
      next := (0)
      square := (2525616328813926360352670715750000000000000)
      linear := (-169134697081988473688907157899825000000000000)
      constant := (2881592861249073432390888187388665284519622825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree097.table
  base := (1635931997369211616211999650678645725591/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (22032)
      previous := (12648)
      next := (0)
      square := (561248073069761413411704603500000000000000)
      linear := (-38439465700642147467092079740450000000000000)
      constant := (669273263754109033300627880574803215367394975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell014.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234697282264178476407/50000000000000000000)
  centralHi := (93878912905671390563/20000000000000000000)
  directionLo := (235916497129470139519/50000000000000000000)
  directionHi := (471832994258940279039/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree098.table
  base := (2185386646939217156176489905872768091293/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32512500000000000000000000000000000000000000
      center := (50184)
      previous := (27846)
      next := (0)
      square := (1262808164406963180176335357875000000000000)
      linear := (-85468646917159206643638257519062500000000000)
      constant := (1472963016848954213471552780836440349027265465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 31
  qDenominator := 85
  table := BinomialMassData.Q31_85.Degree098.table
  base := (4370772810003825489532275569896364566641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (11016)
      previous := (6324)
      next := (0)
      square := (280624036534880706705852301750000000000000)
      linear := (-19424423324028869072555014490325000000000000)
      constant := (342089469784689345324940657307690246798796245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31_85.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell014.Kernel098
