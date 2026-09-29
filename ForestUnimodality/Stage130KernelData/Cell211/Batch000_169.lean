import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell211.Parameters
import ForestUnimodality.BinomialMassData.Q57_107.Batch000_049
import ForestUnimodality.BinomialMassData.Q57_107.Batch050_099
import ForestUnimodality.BinomialMassData.Q57_107.Batch100_149
import ForestUnimodality.BinomialMassData.Q57_107.Batch150_199
import ForestUnimodality.BinomialMassData.Q29_54.Batch000_049
import ForestUnimodality.BinomialMassData.Q29_54.Batch050_099
import ForestUnimodality.BinomialMassData.Q29_54.Batch100_149
import ForestUnimodality.BinomialMassData.Q29_54.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree000.table
  base := (5275481474751975132341463769/100000000000000000000000000)
  polynomial :=
    { denominator := 535000000000000000000000000000000000000000
      center := (3249)
      previous := (0)
      next := (2850)
      square := (45102374879233268004097290295000000000000)
      linear := (-231077085197693412321751083600000000000000)
      constant := (28223825889923066958026831164150000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree000.table
  base := (5275481474751975132341463769/100000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (551)
      previous := (0)
      next := (475)
      square := (7587315400244848823119170330000000000000)
      linear := (-38872780687462443194313266400000000000000)
      constant := (4747933327276777619107317392100000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree001.table
  base := (316177314899251699285647898758046109222853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-59733837704771575341788914077660000000000000)
      constant := (3648995886853558144551208436900399904492443997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree001.table
  base := (314471260201934496173000087553650124453037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-3808791675505759746350742397110000000000000)
      constant := (231117762765215028374076447088553440726263973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (12465659275774314887/25000000000000000000)
  directionHi := (49862637103097259549/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree002.table
  base := (200054202468724618459281055125538746712473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-70017179177236760446723096264920000000000000)
      constant := (2354062222927455816450252129149613111111103377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree002.table
  base := (39639063416222415069225384022240046315017/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-4468888115327061593962110215820000000000000)
      constant := (148575310544340593025258803632034968818236965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12465659275774314887/25000000000000000000)
  centralHi := (49862637103097259549/100000000000000000000)
  directionLo := (35258208823444019841/50000000000000000000)
  directionHi := (70516417646888039683/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree003.table
  base := (134434012507712741192232528716864831630489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-80300520649701945551657278452180000000000000)
      constant := (1642814560073809834750223276272755457337468561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree003.table
  base := (16609454765257684148736781682047514504811/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-569887172794262604619275337170000000000000)
      constant := (11503830125955349139705733066309289399117528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35258208823444019841/50000000000000000000)
  centralHi := (70516417646888039683/100000000000000000000)
  directionLo := (21591155215483368161/25000000000000000000)
  directionHi := (17272924172386694529/20000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree004.table
  base := (95857508741207620828815273107899427142847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-90583862122167130656591460639440000000000000)
      constant := (1246668102180048493690160883760020541358455303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree004.table
  base := (2957949450482104771237617516877858698977/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-5789080994969665289184845853240000000000000)
      constant := (78602878510067635379349748564006687729735456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21591155215483368161/25000000000000000000)
  centralHi := (17272924172386694529/20000000000000000000)
  directionLo := (99725274206194519097/100000000000000000000)
  directionHi := (49862637103097259549/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree005.table
  base := (8998393195414979851346410074572233620949/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-50433601797316157880762821413350000000000000)
      constant := (512185144802171920098284510715235010904980404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree005.table
  base := (35537821196948491556672680485654446132391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-6449177434790967136796213671950000000000000)
      constant := (64700176057178091709560807928646682461026078) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99725274206194519097/100000000000000000000)
  centralHi := (49862637103097259549/50000000000000000000)
  directionLo := (111496246099928661853/100000000000000000000)
  directionHi := (55748123049964330927/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree006.table
  base := (28153668422756365046124048015469593579277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-55575272533548750433229912506980000000000000)
      constant := (450662088380539798079741465124651376889142373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree006.table
  base := (55607712412257036983035016724061194398623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-789919319401363220489731276740000000000000)
      constant := (6340527817729888388287945774418956746288463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111496246099928661853/100000000000000000000)
  centralHi := (55748123049964330927/50000000000000000000)
  directionLo := (12213801813215665899/10000000000000000000)
  directionHi := (122138018132156658991/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree007.table
  base := (11335518773424816067111483923283938668781/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-60716943269781342985697003600610000000000000)
      constant := (418866476925226675237174943215440627637747338) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree007.table
  base := (44789282077872577437858130116039411291299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-7769370314433570832018949309370000000000000)
      constant := (53173306141009477770198018976975230831356971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12213801813215665899/10000000000000000000)
  centralHi := (122138018132156658991/100000000000000000000)
  directionLo := (26384827497731494757/20000000000000000000)
  directionHi := (65962068744328736893/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree008.table
  base := (2325719850543030813752492621453712112771/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-65858614006013935538164094694240000000000000)
      constant := (406037150904713967916609453957948399832921432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree008.table
  base := (3675978073491458386096754580051240583563/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-8429466754254872679630317128080000000000000)
      constant := (51669487393400182506698752702493543854174270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26384827497731494757/20000000000000000000)
  centralHi := (65962068744328736893/50000000000000000000)
  directionLo := (35258208823444019841/25000000000000000000)
  directionHi := (28206567058755215873/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree009.table
  base := (30878139582839655227538507132929928067677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-142000569484493056181262371575740000000000000)
      constant := (812469599115324278179032639558044746446833973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree009.table
  base := (15248748844873236760245509587891388847349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (551)
      previous := (0)
      next := (475)
      square := (7587315400244848823119170330000000000000)
      linear := (-112216829556495981817798579590000000000000)
      constant := (639610703963951122130356133724544999252282) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35258208823444019841/25000000000000000000)
  centralHi := (28206567058755215873/20000000000000000000)
  directionLo := (29917582261858355729/20000000000000000000)
  directionHi := (74793955654645889323/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree010.table
  base := (804763171790056527630207965728346863737/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-76141955478479120643098276881500000000000000)
      constant := (416084718398294481238111158102481491886798608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree010.table
  base := (6355993999183486209001192236531153935703/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-9749659633897476374853052765500000000000000)
      constant := (53168549910681647075649364799974844876509948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29917582261858355729/20000000000000000000)
  centralHi := (74793955654645889323/50000000000000000000)
  directionLo := (39419875847051854551/25000000000000000000)
  directionHi := (31535900677641483641/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree011.table
  base := (21486033379633688800705297227085213203077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-162567252429423426391130735950260000000000000)
      constant := (867185784999428883573419285972028605962028573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree011.table
  base := (21197999999799756836721812853726000314939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-10409756073718778222464420584210000000000000)
      constant := (55500989848924692388266596541408754229590531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39419875847051854551/25000000000000000000)
  centralHi := (31535900677641483641/20000000000000000000)
  directionLo := (82687829164313665251/50000000000000000000)
  directionHi := (165375658328627330503/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree012.table
  base := (714515280033136678407366123844361809907/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-172850593901888611496064918137520000000000000)
      constant := (915044592344257355054330801596872459040631075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree012.table
  base := (17607811498874204549524789424156395560341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-1229983612615564452230643155880000000000000)
      constant := (6516823900884262433889776171236668040387621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82687829164313665251/50000000000000000000)
  centralHi := (165375658328627330503/100000000000000000000)
  directionLo := (21591155215483368161/12500000000000000000)
  directionHi := (172729241723866945289/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree013.table
  base := (14741313497913304264624885815346739653267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-183133935374353796600999100324780000000000000)
      constant := (974124063754129039436202886258074822290253883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree013.table
  base := (14514299296779075481822614351056405400287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-11729948953361381917687156221630000000000000)
      constant := (62518413625039738718774631339802619536809223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21591155215483368161/12500000000000000000)
  centralHi := (172729241723866945289/100000000000000000000)
  directionLo := (179782294805070360357/100000000000000000000)
  directionHi := (89891147402535180179/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree014.table
  base := (6011560664262991836719963983493144270109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-96708638423409490852966641256020000000000000)
      constant := (521649916262768598235674240294553008748477941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree014.table
  base := (1477588624242300732981533910468555916347/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-12390045393182683765298524040340000000000000)
      constant := (67031451442877945241409295017782618104135704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179782294805070360357/100000000000000000000)
  centralHi := (89891147402535180179/50000000000000000000)
  directionLo := (93284452220416131557/50000000000000000000)
  directionHi := (37313780888166452623/20000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree015.table
  base := (9636654790389961089784323658536377175641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-203700618319284166810867464699300000000000000)
      constant := (1121751569768118245244989684576832982283913809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree015.table
  base := (2364052068849269388962766486850292450743/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-1450015759222665068101099095450000000000000)
      constant := (8015432422652300038780552494301994754040732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93284452220416131557/50000000000000000000)
  centralHi := (37313780888166452623/20000000000000000000)
  directionLo := (48279290774569931031/25000000000000000000)
  directionHi := (1544937304786237793/800000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree016.table
  base := (3763695255278417653430768190346060068301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-106991979895874675957900823443280000000000000)
      constant := (604427518692492970170256475863112041721978149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree016.table
  base := (1841684740762034482079168406028867413061/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-13710238272825287460521259677760000000000000)
      constant := (77801326296178035574714468913260177376485876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48279290774569931031/25000000000000000000)
  centralHi := (1544937304786237793/800000000000000000)
  directionLo := (99725274206194519097/50000000000000000000)
  directionHi := (39890109682477807639/20000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree017.table
  base := (5652491658696467662500934005425381334287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-224267301264214537020735829073820000000000000)
      constant := (1304119796505690524214726714803485190896251863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree017.table
  base := (5509740981548252436150691862857666521657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-14370334712646589308132627496470000000000000)
      constant := (83987728624874660035101049024605738894287953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99725274206194519097/50000000000000000000)
  centralHi := (39890109682477807639/20000000000000000000)
  directionLo := (41117783909582439923/20000000000000000000)
  directionHi := (3212326867936128119/1562500000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree018.table
  base := (3977529121191153133933840180796569131253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-234550642736679722125670011261080000000000000)
      constant := (1407151668208422892061952398255259919983715597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree018.table
  base := (770193274704256079001362990732799587571/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (551)
      previous := (0)
      next := (475)
      square := (7587315400244848823119170330000000000000)
      linear := (-185560878425529520441283892780000000000000)
      constant := (1119421383074486014460447603952975981440695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41117783909582439923/20000000000000000000)
  centralHi := (3212326867936128119/1562500000000000000)
  directionLo := (105774626470332059523/50000000000000000000)
  directionHi := (211549252940664119047/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree019.table
  base := (494880050821471907137842899663118305041/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-244833984209144907230604193448340000000000000)
      constant := (1517628905322788033890732060444745207372072045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree019.table
  base := (118122404765282566265740440315769202747/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-15690527592289193003355363133890000000000000)
      constant := (97837148533824872103693388948246414976051260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105774626470332059523/50000000000000000000)
  centralHi := (211549252940664119047/100000000000000000000)
  directionLo := (217346196190842635799/100000000000000000000)
  directionHi := (1086730980954213179/500000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree020.table
  base := (559965753525826805062837851465443270857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-127558662840805046167769187817800000000000000)
      constant := (817643096935165766167164763691427860008041793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree020.table
  base := (40845125390221497945939966723061920761/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-16350624032110494850966730952600000000000000)
      constant := (105462968848394866381819767078527803505869225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217346196190842635799/100000000000000000000)
  centralHi := (1086730980954213179/500000000000000000)
  directionLo := (111496246099928661853/50000000000000000000)
  directionHi := (222992492199857323707/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree021.table
  base := (-21022457445014600143111003197064917539/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-265400667154075277440472557822860000000000000)
      constant := (1759903310421218345802474740466714018795479945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree021.table
  base := (-24015158388152768037631180971245786203/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-1890080052436866299842010974590000000000000)
      constant := (12615183204049969855865464037913132730540456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111496246099928661853/50000000000000000000)
  centralHi := (222992492199857323707/100000000000000000000)
  directionLo := (114249654437528388551/50000000000000000000)
  directionHi := (228499308875056777103/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree022.table
  base := (-304191114723947158604301362865271768501/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-137842004313270231272703370005060000000000000)
      constant := (945648344689149079899091524596971007044864102) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree022.table
  base := (-40413418531157274367587441355028034303/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-17670816911753098546189466590020000000000000)
      constant := (122046576050886283583780704107439906015779616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114249654437528388551/50000000000000000000)
  centralHi := (228499308875056777103/100000000000000000000)
  directionLo := (46775299778944772591/20000000000000000000)
  directionHi := (58469124723680965739/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree023.table
  base := (-1114212568832134914352171213789176008691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-142983675049502823825170461098690000000000000)
      constant := (1014656456328296218370520081747812723876496741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree023.table
  base := (-114774723380028155555962311836763353237/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-18330913351574400393800834408730000000000000)
      constant := (130983056085912323576478508330602490309804540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46775299778944772591/20000000000000000000)
  centralHi := (58469124723680965739/25000000000000000000)
  directionLo := (47826561370907251859/20000000000000000000)
  directionHi := (7472900214204258103/3125000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree024.table
  base := (-3151312635282827546280487235270886321767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-296250691571470832755275104384640000000000000)
      constant := (2173823541804848968419053468111863622502089617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree024.table
  base := (-802508850533179900726657153992422106861/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-2110112199043966915712466914160000000000000)
      constant := (15593109250583413763137297091226455237377036) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47826561370907251859/20000000000000000000)
  centralHi := (7472900214204258103/3125000000000000000)
  directionLo := (12213801813215665899/5000000000000000000)
  directionHi := (244276036264313317981/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree025.table
  base := (-3994828764751521373587749746939927853157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-306534033043936017860209286571900000000000000)
      constant := (2324720935466030072627047247113534766009205507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree025.table
  base := (-4046158027273927100200739429353466014613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-19651106231217004089023570046150000000000000)
      constant := (150104573608335454746991946630063823275347123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12213801813215665899/5000000000000000000)
  centralHi := (244276036264313317981/100000000000000000000)
  directionLo := (249313185515486297743/100000000000000000000)
  directionHi := (15582074094717893609/6250000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree026.table
  base := (-4766858373260691182015829907879933581333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-316817374516401202965143468759160000000000000)
      constant := (2481914820024653548177480825826962640427318483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree026.table
  base := (-4811655588283257313337786959016348393177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-20311202671038305936634937864860000000000000)
      constant := (160277145869372652935912230920007082021373967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249313185515486297743/100000000000000000000)
  centralHi := (15582074094717893609/6250000000000000000)
  directionLo := (50850111917577706807/20000000000000000000)
  directionHi := (63562639896972133509/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree027.table
  base := (-5474017030467183015457955182247971404683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-327100715988866388070077650946420000000000000)
      constant := (2645329453823718164713820643015012975387784333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree027.table
  base := (-5513057225032251496411906998935822505939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (551)
      previous := (0)
      next := (475)
      square := (7587315400244848823119170330000000000000)
      linear := (-258904927294563059064769205970000000000000)
      constant := (2109270867844394627910640761692077597446549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50850111917577706807/20000000000000000000)
  centralHi := (63562639896972133509/25000000000000000000)
  directionLo := (64773465646450104483/25000000000000000000)
  directionHi := (259093862585800417933/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree028.table
  base := (-382616060484851997893481200347278943197/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-168692028730665786587505916566840000000000000)
      constant := (1407450634683039168531695031062352027034700376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree028.table
  base := (-9618491345910559002246269625129887343/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-21631395550680909631857673502280000000000000)
      constant := (181821968145510103247882378976219399761249920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64773465646450104483/25000000000000000000)
  centralHi := (259093862585800417933/100000000000000000000)
  directionLo := (263848274977314947571/100000000000000000000)
  directionHi := (65962068744328736893/25000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree029.table
  base := (-1678759725783012434807947891070797135769/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-173833699466898379139973007660470000000000000)
      constant := (1495288453045675965609523766060225887185161438) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree029.table
  base := (-3372286669617490210623285901875651077039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-22291491990502211479469041320990000000000000)
      constant := (193186886195169819153219376667907800729677138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263848274977314947571/100000000000000000000)
  centralHi := (65962068744328736893/25000000000000000000)
  directionLo := (134259259259259259259/50000000000000000000)
  directionHi := (268518518518518518519/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree030.table
  base := (-1814368930180797819070744280997975455633/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-178975370203130971692440098754100000000000000)
      constant := (1586155782694551517924821670518208358016915566) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree030.table
  base := (-3641559099059317661220068026903387616467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-2550176492258168147453378793300000000000000)
      constant := (22771432435650883302733389961891651206132346) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134259259259259259259/50000000000000000000)
  centralHi := (268518518518518518519/100000000000000000000)
  directionLo := (273108911180604182117/100000000000000000000)
  directionHi := (136554455590302091059/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree031.table
  base := (-310098111389866548779550943399869111993/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-368234081878727128489814379695460000000000000)
      constant := (3360067633124427164785967050721702463419803575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree031.table
  base := (-1943672980507522850521536458301898330847/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-23611684870144815174691776958410000000000000)
      constant := (217087635840141142006903322202334164467250148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273108911180604182117/100000000000000000000)
  centralHi := (136554455590302091059/50000000000000000000)
  directionLo := (8675731684354716357/3125000000000000000)
  directionHi := (11104936555974036937/4000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree032.table
  base := (-1640545755729225457361204886222213015481/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-378517423351192313594748561882720000000000000)
      constant := (3553813525130577852192630760130129415928790155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree032.table
  base := (-513874786620995935055737027297293340401/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-24271781309966117022303144777120000000000000)
      constant := (229619148140368754586912271849924370477562736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8675731684354716357/3125000000000000000)
  centralHi := (11104936555974036937/4000000000000000000)
  directionLo := (35258208823444019841/12500000000000000000)
  directionHi := (282065670587552158729/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree033.table
  base := (-8610620271142062501558029218813823298683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-388800764823657498699682744069980000000000000)
      constant := (3753522719012274316558106012639570537053378333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree033.table
  base := (-2156824435138729413661535631622129446163/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-2770208638865268763323834732870000000000000)
      constant := (26948419692785201945284125444796930059443188) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35258208823444019841/12500000000000000000)
  centralHi := (282065670587552158729/100000000000000000000)
  directionLo := (11457561702413347837/4000000000000000000)
  directionHi := (143219521280166847963/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree034.table
  base := (-897807266254089650808303666323512928961/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-199542053148061341902308463128620000000000000)
      constant := (1979586470940704136753432099355250502381627555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree034.table
  base := (-8992495019430723559472240112370384281767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-25591974189608720717525880414540000000000000)
      constant := (255836138291381985077344194578811989858591857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11457561702413347837/4000000000000000000)
  centralHi := (143219521280166847963/50000000000000000000)
  directionLo := (290746638298288549453/100000000000000000000)
  directionHi := (145373319149144274727/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree035.table
  base := (-4653359860108210391703804654026870047309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-204683723884293934454775554222250000000000000)
      constant := (2085372744367658592209214101890171364828359259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree035.table
  base := (-9319181301593505213627621424263981092103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-26252070629430022565137248233250000000000000)
      constant := (269519070100501276095883724665274057783856913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290746638298288549453/100000000000000000000)
  centralHi := (145373319149144274727/50000000000000000000)
  directionLo := (147495669648833251239/50000000000000000000)
  directionHi := (294991339297666502479/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree036.table
  base := (-599870846719237852209130730041980250937/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-209825394620526527007242645315880000000000000)
      constant := (2194112325181435444219315798677434944856178296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree036.table
  base := (-960869229280208123637918774085265375327/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (551)
      previous := (0)
      next := (475)
      square := (7587315400244848823119170330000000000000)
      linear := (-332248976163596597688254519160000000000000)
      constant := (3501032085591685330737409237412326116220570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147495669648833251239/50000000000000000000)
  centralHi := (294991339297666502479/100000000000000000000)
  directionLo := (299175822618583557291/100000000000000000000)
  directionHi := (74793955654645889323/25000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree037.table
  base := (-1970573305732658274900400580492749796309/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-429934130713518239119419472819020000000000000)
      constant := (4611597233116811282251374689013462537910291295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree037.table
  base := (-2465537020490906098352667858521925219577/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-27572263509072626260359983870670000000000000)
      constant := (298028908243844363212700024375032566059713468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299175822618583557291/100000000000000000000)
  centralHi := (74793955654645889323/25000000000000000000)
  directionLo := (303302580632577777457/100000000000000000000)
  directionHi := (151651290316288888729/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree038.table
  base := (-2014497308340671671035600301096244643793/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-440217472185983424224353655006280000000000000)
      constant := (4840852155761681886280246341222665475366069715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree038.table
  base := (-10080487974668593008210693816330372143507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-28232359948893928107971351689380000000000000)
      constant := (312854313279479386246970148162465158707383397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303302580632577777457/100000000000000000000)
  centralHi := (151651290316288888729/50000000000000000000)
  directionLo := (307373938383293185429/100000000000000000000)
  directionHi := (30737393838329318543/10000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree039.table
  base := (-1282200815239459841746308729520114964703/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-225250406829224304664643918596770000000000000)
      constant := (2537990055500687071002187286249061815076461412) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree039.table
  base := (-2566124923378059540578079394192988425083/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-3210272932079469995064746612010000000000000)
      constant := (36451026643339960317122546321363971750273108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307373938383293185429/100000000000000000000)
  centralHi := (30737393838329318543/10000000000000000000)
  directionLo := (311392068903708090641/100000000000000000000)
  directionHi := (155696034451854045321/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree040.table
  base := (-10408909283857846568497883634286211409383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-460784155130913794434222019380800000000000000)
      constant := (5316973281292018155058085454095057165573974033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree040.table
  base := (-416593754304793270658812188661187858827/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-29552552828536531803194087326800000000000000)
      constant := (343643206184242809811158109065649851272877925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311392068903708090641/100000000000000000000)
  centralHi := (155696034451854045321/50000000000000000000)
  directionLo := (315359006776414836409/100000000000000000000)
  directionHi := (31535900677641483641/10000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree041.table
  base := (-10526968363400908532524277213826755824007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-471067496603378979539156201568060000000000000)
      constant := (5563825100221426312073454557152827472570943857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree041.table
  base := (-5266037252801101701103603575621609587581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-30212649268357833650805455145510000000000000)
      constant := (359605808567881592353205784336086193221306902) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315359006776414836409/100000000000000000000)
  centralHi := (31535900677641483641/10000000000000000000)
  directionLo := (159638330088580253679/50000000000000000000)
  directionHi := (319276660177160507359/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree042.table
  base := (-1326533189843158153180052004782023320027/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-240675419037922082322045191877660000000000000)
      constant := (2908265026069981113294028503940062460036043508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree042.table
  base := (-10616656302181436720408652225461920090839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-3430305078686570610935202551580000000000000)
      constant := (41771856466710399055416702263267584472642041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159638330088580253679/50000000000000000000)
  centralHi := (319276660177160507359/100000000000000000000)
  directionLo := (161573410801992109247/50000000000000000000)
  directionHi := (64629364320796843699/20000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree043.table
  base := (-5332602713284526346653388266940405295089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-245817089774154674874512282971290000000000000)
      constant := (3037541751952168959505273205836084299776526039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree043.table
  base := (-5334489482469059721406251986049960046929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-31532842148000437346028190782930000000000000)
      constant := (392665620977662558798644814285621658251577518) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161573410801992109247/50000000000000000000)
  centralHi := (64629364320796843699/20000000000000000000)
  directionLo := (65394235492628055683/20000000000000000000)
  directionHi := (20435698591446267401/6250000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree044.table
  base := (-2671532005821584199569283160892268778941/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-250958760510387267426979374064920000000000000)
      constant := (3169740781791274374642562105328528829499808982) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree044.table
  base := (-10689369360721087634664043336433409341291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-32192938587821739193639558601640000000000000)
      constant := (409762308613755692761325456275620044590198861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65394235492628055683/20000000000000000000)
  centralHi := (20435698591446267401/6250000000000000000)
  directionLo := (66150263331450932201/20000000000000000000)
  directionHi := (165375658328627330503/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree045.table
  base := (-10675318869100904351917158347173229948977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-512200862493239719958892930317100000000000000)
      constant := (6609720961795821562206175003439463690314162327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree045.table
  base := (-5339050824232933395893615746912019996697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (551)
      previous := (0)
      next := (475)
      square := (7587315400244848823119170330000000000000)
      linear := (-405593025032630136311739832350000000000000)
      constant := (5274525570948259201238723193118083640059454) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66150263331450932201/20000000000000000000)
  centralHi := (165375658328627330503/50000000000000000000)
  directionLo := (334488738299785985559/100000000000000000000)
  directionHi := (8362218457494649639/2500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree046.table
  base := (-1063301785189007017061935301186960825149/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-261242101982852452531913556252180000000000000)
      constant := (3442899476033924490220410532382292427564345495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree046.table
  base := (-53177028920927781016194964511711916771/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-33513131467464342888862294239060000000000000)
      constant := (445088241238888917033955683456522402534788200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334488738299785985559/100000000000000000000)
  centralHi := (8362218457494649639/2500000000000000000)
  directionLo := (4227310733275387567/1250000000000000000)
  directionHi := (338184858662031005361/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree047.table
  base := (-2111885299411977185841214190424138830547/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-532767545438170090168761294691620000000000000)
      constant := (7167713227134257118364021260086140172645336985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree047.table
  base := (-5280737326402021811441878435768560529297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-34173227907285644736473662057770000000000000)
      constant := (463317177976885943789615601750831938748284974) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4227310733275387567/1250000000000000000)
  centralHi := (338184858662031005361/100000000000000000000)
  directionLo := (68368203488795303867/20000000000000000000)
  directionHi := (42730127180497064917/12500000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree048.table
  base := (-1045471410680340093783007629225740192557/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-271525443455317637636847738439440000000000000)
      constant := (3727730924327118877211918296472332502677074535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree048.table
  base := (-2614117512172014368441077925717599364653/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-3870369371900771842676114430720000000000000)
      constant := (53547029279189636727435348983747497805852428) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68368203488795303867/20000000000000000000)
  centralHi := (42730127180497064917/12500000000000000000)
  directionLo := (21591155215483368161/6250000000000000000)
  directionHi := (345458483447733890577/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree049.table
  base := (-10319022916347936539189908070017433026487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-553334228383100460378629659066140000000000000)
      constant := (7749043188176673286567711489897100409279750337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree049.table
  base := (-10320527690856471919391924028500146081679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-35493420786928248431696397695190000000000000)
      constant := (500906398907186518040663587390365893506456009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21591155215483368161/6250000000000000000)
  centralHi := (345458483447733890577/100000000000000000000)
  directionLo := (8725961493042020421/2500000000000000000)
  directionHi := (349038459721680816841/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree050.table
  base := (-10152472424690115121478331022616739461451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-563617569855565645483563841253400000000000000)
      constant := (8048455877557551385073226987467060949905847501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree050.table
  base := (-507688071438836020750820977174388747391/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-36153517226749550279307765513900000000000000)
      constant := (520266501164063547281974818429047412063039220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8725961493042020421/2500000000000000000)
  centralHi := (349038459721680816841/100000000000000000000)
  directionLo := (35258208823444019841/10000000000000000000)
  directionHi := (352582088234440198411/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree051.table
  base := (-2488790758015444915101829166403416517837/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-286950455664015415294249011720330000000000000)
      constant := (4176849383657308839855728361886459568574568374) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree051.table
  base := (-9956266769456733098887670689618625190731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-4090401518507872458546570370290000000000000)
      constant := (60000388962081004133340852995523391359550789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35258208823444019841/10000000000000000000)
  centralHi := (352582088234440198411/100000000000000000000)
  directionLo := (356090454130174268641/100000000000000000000)
  directionHi := (178045227065087134321/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree052.table
  base := (-9727179095168728256685677591483585779949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-584184252800496015693432205627920000000000000)
      constant := (8664770891647947488027385503443424426405363899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree052.table
  base := (-76000967464198280358588416747087514303/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-37473710106392153974530501151320000000000000)
      constant := (560117338981865273626984699512215769865358464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356090454130174268641/100000000000000000000)
  centralHi := (178045227065087134321/50000000000000000000)
  directionLo := (179782294805070360357/50000000000000000000)
  directionHi := (71912917922028144143/20000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree053.table
  base := (-4734295746722746432742529362044648405143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-297233797136480600399183193907590000000000000)
      constant := (4490835719529447426833126581872635820409517793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree053.table
  base := (-9469399845424106491375188540971653592567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-38133806546213455822141868970030000000000000)
      constant := (580607967130992246636254814719714164531018657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179782294805070360357/50000000000000000000)
  centralHi := (71912917922028144143/20000000000000000000)
  directionLo := (363005477479864052521/100000000000000000000)
  directionHi := (181502738739932026261/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree054.table
  base := (-9179459784626379216603888125817262974719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-604750935745426385903300570002440000000000000)
      constant := (9304399727670959710327597501792198156202442169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree054.table
  base := (-1836030239002750036265068800801903340769/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (551)
      previous := (0)
      next := (475)
      square := (7587315400244848823119170330000000000000)
      linear := (-478937073901663674935225145540000000000000)
      constant := (7425621530787204961246378877093914349665395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363005477479864052521/100000000000000000000)
  centralHi := (181502738739932026261/50000000000000000000)
  directionLo := (36641405439646997697/10000000000000000000)
  directionHi := (366414054396469976971/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree055.table
  base := (-8859834015386881228768222931547231377363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-615034277217891571008234752189700000000000000)
      constant := (9632955184499754328135923889446965747960571013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree055.table
  base := (-1107553150176213723807683145666149323763/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-39453999425856059517364604607450000000000000)
      constant := (622719435075923481550585506722537517143814184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36641405439646997697/10000000000000000000)
  centralHi := (366414054396469976971/100000000000000000000)
  directionLo := (184895606923294983087/50000000000000000000)
  directionHi := (14791648553863598647/4000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree056.table
  base := (-4254878121137724855567858015474757255727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-312658809345178378056584467188480000000000000)
      constant := (4983668664019927746888593179387869504179181577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree056.table
  base := (-8510261566987232425650140204868105895377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-40114095865677361364975972426160000000000000)
      constant := (644340211434440330564235524970331150802270167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (184895606923294983087/50000000000000000000)
  centralHi := (14791648553863598647/4000000000000000000)
  directionLo := (373137808881664526229/100000000000000000000)
  directionHi := (37313780888166452623/10000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree057.table
  base := (-4064630904655207845680357599067134714667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-317800480081410970609051558282110000000000000)
      constant := (5153772876818798667657885141056365374651777517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree057.table
  base := (-4064846803352533196987731131512279473383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-4530465811722073690287482249430000000000000)
      constant := (74037516531412135709560271098737510725311954) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373137808881664526229/100000000000000000000)
  centralHi := (37313780888166452623/10000000000000000000)
  directionLo := (376454654634372629193/100000000000000000000)
  directionHi := (188227327317186314597/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree058.table
  base := (-7718380421189565446183872143603291865923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-645884301635287126323037298751480000000000000)
      constant := (10653580121203894897669271938024405911427047573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree058.table
  base := (-7718749277587367798516834889619227456153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-41434288745319965060198708063580000000000000)
      constant := (688711726740059544216861366289637583184464463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376454654634372629193/100000000000000000000)
  centralHi := (188227327317186314597/50000000000000000000)
  directionLo := (379742530637219966807/100000000000000000000)
  directionHi := (47467816329652495851/12500000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree059.table
  base := (-7277137044822928943345775767703637249939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-656167643107752311427971480938740000000000000)
      constant := (11005440144892595247737029324190691057125448389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree059.table
  base := (-7277452042191974465902184587048078680763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-42094385185141266907810075882290000000000000)
      constant := (711462428202286635281080545753084450641723773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (379742530637219966807/100000000000000000000)
  centralHi := (47467816329652495851/12500000000000000000)
  directionLo := (191501091480985504981/50000000000000000000)
  directionHi := (383002182961971009963/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree060.table
  base := (-3402776333330910488621515466388510250553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-333225492290108748266452831563000000000000000)
      constant := (5681562792214908641218997855771317946141418703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree060.table
  base := (-6805821592846427516997880398727917465519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-4750497958329174306157938189000000000000000)
      constant := (81621082090409301900176488360703038685292961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191501091480985504981/50000000000000000000)
  centralHi := (383002182961971009963/100000000000000000000)
  directionLo := (386234326196559448249/100000000000000000000)
  directionHi := (1544937304786237793/400000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree061.table
  base := (-1575911232224694955737564377818387167909/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-338367163026341340818919922656630000000000000)
      constant := (5863318118915049315530420888580279570629219718) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree061.table
  base := (-6303874459110890104605214291941175204773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-43414578064783870603032811519710000000000000)
      constant := (758093646524201430739992772925217383275720483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386234326196559448249/100000000000000000000)
  centralHi := (1544937304786237793/400000000000000000)
  directionLo := (77887929054863298383/20000000000000000000)
  directionHi := (97359911318579122979/25000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree062.table
  base := (-721428582989904079600931735020661776361/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-343508833762573933371387013750260000000000000)
      constant := (6047985967638729269046315439813253773289771644) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree062.table
  base := (-5771624517302828561652104307761811202919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-44074674504605172450644179338420000000000000)
      constant := (781974141218004343239589226537811639633072049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77887929054863298383/20000000000000000000)
  centralHi := (97359911318579122979/25000000000000000000)
  directionLo := (196309398584390650031/50000000000000000000)
  directionHi := (392618797168781300063/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree063.table
  base := (-325557271455220518283119814526947496021/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-348650504498806525923854104843890000000000000)
      constant := (6235566266992501284639098291833932824944444568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree063.table
  base := (-5209083417879198007184608690083673183239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (551)
      previous := (0)
      next := (475)
      square := (7587315400244848823119170330000000000000)
      linear := (-552281122770697213558710458730000000000000)
      constant := (9953471782739621411340656538571746941350849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196309398584390650031/50000000000000000000)
  centralHi := (392618797168781300063/100000000000000000000)
  directionLo := (395772412465972421357/100000000000000000000)
  directionHi := (197886206232986210679/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree064.table
  base := (-4616118454912590683930270903355319644927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-707584350470078236952642391875040000000000000)
      constant := (12852117913876524066957278157849564945385230777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree064.table
  base := (-2308130471961685145928181176776189658729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-45394867384247776145866914975840000000000000)
      constant := (830864858944048625897878132331940315477573118) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (395772412465972421357/100000000000000000000)
  centralHi := (197886206232986210679/50000000000000000000)
  directionLo := (99725274206194519097/25000000000000000000)
  directionHi := (398901096824778076389/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree065.table
  base := (-3993043819962245650692033638574670139419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-717867691942543422057576574062300000000000000)
      constant := (13238927973958609981091339002922208601573791869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree065.table
  base := (-3993165311846903617370878472741238844313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-46054963824069077993478282794550000000000000)
      constant := (855875068854658192048402223556434136882495823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99725274206194519097/25000000000000000000)
  centralHi := (398901096824778076389/100000000000000000000)
  directionLo := (201002716167522314283/50000000000000000000)
  directionHi := (402005432335044628567/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree066.table
  base := (-333969985903341886351749127223138142913/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-364075516707504303581255378124780000000000000)
      constant := (6815781314636400156838254323040451457008945315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree066.table
  base := (-13046107123531406685903677935618199337/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-5190562251543375537898850068140000000000000)
      constant := (97917982122466534473217021310497021018547968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201002716167522314283/50000000000000000000)
  centralHi := (402005432335044628567/100000000000000000000)
  directionLo := (81017195756397620917/20000000000000000000)
  directionHi := (202542989390994052293/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree067.table
  base := (-664023203955441340910056944868493897201/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-369217187443736896133722469218410000000000000)
      constant := (7015010904167511755072851892197086226741891502) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree067.table
  base := (-132809053918691465866033216449853726163/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-47375156703711681688701018431970000000000000)
      constant := (907025165459112693412827713659243632672543460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81017195756397620917/20000000000000000000)
  centralHi := (202542989390994052293/50000000000000000000)
  directionLo := (408143274824707222371/100000000000000000000)
  directionHi := (102035818706176805593/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree068.table
  base := (-194222794501374723643637112832446466333/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-374358858179969488686189560312040000000000000)
      constant := (7217152725492187133041726564378066602034767415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree068.table
  base := (-242787893730539100860606070810037495331/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-48035253143532983536312386250680000000000000)
      constant := (933165044372437519203800133866755861327229608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408143274824707222371/100000000000000000000)
  centralHi := (102035818706176805593/25000000000000000000)
  directionLo := (411177839095824399231/100000000000000000000)
  directionHi := (3212326867936128119/781250000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree069.table
  base := (-74881854384196961695722692898358856997/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-379500528916202081238656651405670000000000000)
      constant := (7422206753287884229605914153284818515569930776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree069.table
  base := (-1198173735296114266901551359224421139813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-5410594398150476153769306007710000000000000)
      constant := (106631274761696699218258464488285321887675147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411177839095824399231/100000000000000000000)
  centralHi := (3212326867936128119/781250000000000000)
  directionLo := (414190171228611883481/100000000000000000000)
  directionHi := (207095085614305941741/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree070.table
  base := (-52967714529912983709535271417283407831/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-384642199652434673791123742499300000000000000)
      constant := (7630172966230741361769575144642674089054971524) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree070.table
  base := (-423796280396231865941645498895361253399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-49355446023175587231535121888100000000000000)
      constant := (986574448395719773029517686977555281646272129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414190171228611883481/100000000000000000000)
  centralHi := (207095085614305941741/50000000000000000000)
  directionLo := (417180752817363330889/100000000000000000000)
  directionHi := (41718075281736333089/10000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree071.table
  base := (380872778782115300646525990498401081921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-779567740777334532687181667185860000000000000)
      constant := (15682102692715383050570444632427946193986913529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree071.table
  base := (380826316010700559429149380797034578861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-50015542462996889079146489706810000000000000)
      constant := (1013843968880528221332518244002743538207989669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417180752817363330889/100000000000000000000)
  centralHi := (41718075281736333089/10000000000000000000)
  directionLo := (420150048316238057541/100000000000000000000)
  directionHi := (210075024158119028771/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree072.table
  base := (1215731170456157657683857033470527980297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-789851082249799717792115849373120000000000000)
      constant := (16109683757061036041316725589014924074846420353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree072.table
  base := (607845807005005378994582919135102977269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (551)
      previous := (0)
      next := (475)
      square := (7587315400244848823119170330000000000000)
      linear := (-625625171639730752182195771920000000000000)
      constant := (12857901636185158540767743900064431853590842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420150048316238057541/100000000000000000000)
  centralHi := (210075024158119028771/50000000000000000000)
  directionLo := (105774626470332059523/25000000000000000000)
  directionHi := (423098505881328238093/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree073.table
  base := (20808312291262311338501442264755980871/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-400067211861132451448525015780190000000000000)
      constant := (8271544549985551686598103002770944561249603950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree073.table
  base := (2080797558882782222869487417845847910757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-51335735342639492774369225344230000000000000)
      constant := (1069512637849238544305017282588792123126941853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105774626470332059523/25000000000000000000)
  centralHi := (423098505881328238093/100000000000000000000)
  directionLo := (17041062326410875123/4000000000000000000)
  directionHi := (106506639540067969519/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree074.table
  base := (186010692115394000904695814604854303953/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-405208882597365044000992106873820000000000000)
      constant := (8491159349955316964553813068914027815407663176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree074.table
  base := (46502225300747524754535564079032203121/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-51995831782460794621980593162940000000000000)
      constant := (1097911783573073453454438822138001326468813376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17041062326410875123/4000000000000000000)
  centralHi := (106506639540067969519/25000000000000000000)
  directionLo := (428934623033350723023/100000000000000000000)
  directionHi := (26808413939584420189/6250000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree075.table
  base := (1950874558423136574227455209172047488627/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-410350553333597636553459197967450000000000000)
      constant := (8713686269350623899036998642757935771697290523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree075.table
  base := (3901724735165849464582532973624858858803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-5850658691364677385510217886850000000000000)
      constant := (125187496515356310093792352704926113567563043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (428934623033350723023/100000000000000000000)
  centralHi := (26808413939584420189/6250000000000000000)
  directionLo := (21591155215483368161/5000000000000000000)
  directionHi := (431823104309667363221/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree076.table
  base := (97151280337368617430794038216657621/200000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-415492224069830229105926289061080000000000000)
      constant := (8939125300493442742523661890351202827570725000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree076.table
  base := (2428771637299993838817641182931812054779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-53316024662103398317203328800360000000000000)
      constant := (1155839692146483716016419437944594581975867782) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21591155215483368161/5000000000000000000)
  centralHi := (431823104309667363221/100000000000000000000)
  directionLo := (217346196190842635799/50000000000000000000)
  directionHi := (434692392381685271599/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree077.table
  base := (2921807319978455465873223492974474569263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-420633894806062821658393380154710000000000000)
      constant := (9167476436892443138654325781717349759343492087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree077.table
  base := (5843596996886557873330172328971911970357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-53976121101924700164814696619070000000000000)
      constant := (1185368453339260392874067334368103023826390253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217346196190842635799/50000000000000000000)
  centralHi := (434692392381685271599/100000000000000000000)
  directionLo := (218771432420567769967/50000000000000000000)
  directionHi := (87508572968227107987/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree078.table
  base := (1714975006627190257608258784973807405379/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-425775565542295414210860471248340000000000000)
      constant := (9398739673054377986995413555277390241968368342) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree078.table
  base := (3429942511042947423851884468015520160921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-6070690837971778001380673826420000000000000)
      constant := (135030416841673422831487280031348514266069202) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218771432420567769967/50000000000000000000)
  centralHi := (87508572968227107987/20000000000000000000)
  directionLo := (440374887059041293017/100000000000000000000)
  directionHi := (220187443529520646509/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree079.table
  base := (494151210224111675903838829256075538599/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-430917236278528006763327562341970000000000000)
      constant := (9632915004325582593972386471830187470731359608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree079.table
  base := (7906406605266082988198857327596752312939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-55296313981567303860037432256490000000000000)
      constant := (1245555586310829587362819786054160532436132531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440374887059041293017/100000000000000000000)
  centralHi := (220187443529520646509/50000000000000000000)
  directionLo := (443188812732382208033/100000000000000000000)
  directionHi := (221594406366191104017/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree080.table
  base := (898317196164634197019745296241203299053/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-436058907014760599315794653435600000000000000)
      constant := (9870002426758775805262845825915327682854288985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree080.table
  base := (8983161114924691892595149672812434113469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-55956410421388605707648800075200000000000000)
      constant := (1276213957086201466749151541855480264468718901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443188812732382208033/100000000000000000000)
  centralHi := (221594406366191104017/50000000000000000000)
  directionLo := (111496246099928661853/25000000000000000000)
  directionHi := (445984984399714647413/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree081.table
  base := (2522539308747668879629213587936666437871/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-441200577750993191868261744529230000000000000)
      constant := (10110001937001119396386794700308738788094370158) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree081.table
  base := (5045074007440925774905111474766033284299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (551)
      previous := (0)
      next := (475)
      square := (7587315400244848823119170330000000000000)
      linear := (-698969220508764290805681085110000000000000)
      constant := (16138874858151868128448169151888288599117382) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111496246099928661853/25000000000000000000)
  centralHi := (445984984399714647413/100000000000000000000)
  directionLo := (448763733927875335937/100000000000000000000)
  directionHi := (224381866963937667969/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree082.table
  base := (11227374685326384561409526482617546330369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-892684496974451568841457671245720000000000000)
      constant := (20705827064400277013909148567102408287936394681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree082.table
  base := (2245473369817087863387956003732830252703/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-57276603301031209402871535712620000000000000)
      constant := (1338660305250667144921593031782176166271102435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (448763733927875335937/100000000000000000000)
  centralHi := (224381866963937667969/50000000000000000000)
  directionLo := (451525382971726253267/100000000000000000000)
  directionHi := (112881345742931563317/25000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree083.table
  base := (12394823887955397551569170301477757658259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-902967838446916753946391853432980000000000000)
      constant := (21197474419849298052787259333421388847429407291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree083.table
  base := (6197408614429640247237007371060186392153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-57936699740852511250482903531330000000000000)
      constant := (1370448282023954014945082884618488251759759074) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451525382971726253267/100000000000000000000)
  centralHi := (112881345742931563317/25000000000000000000)
  directionLo := (454270243408743681079/100000000000000000000)
  directionHi := (11356756085218592027/2500000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree084.table
  base := (6796252240081809187310510613102877719197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-456625589959690969525663017810120000000000000)
      constant := (10847472968098294111497222509936854847007086453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree084.table
  base := (13592498822200864675416719051525889797681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-6510755131185979233121585705560000000000000)
      constant := (155845865954236899820896780458893597073612161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454270243408743681079/100000000000000000000)
  centralHi := (11356756085218592027/2500000000000000000)
  directionLo := (91399723550022710841/20000000000000000000)
  directionHi := (228499308875056777103/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree085.table
  base := (14820416151461321709696138395382921177611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-923534521391847124156260217807500000000000000)
      constant := (22198241609887350659332077122536989064562468339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree085.table
  base := (14820411344798493835192903493439761107801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-59256892620495114945705639168750000000000000)
      constant := (1435153839735938167390642283005280085847586929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91399723550022710841/20000000000000000000)
  centralHi := (228499308875056777103/50000000000000000000)
  directionLo := (229855399764933505227/50000000000000000000)
  directionHi := (91942159905973402091/20000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree086.table
  base := (2009819829422330453448375846367992419001/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-466908931432156154630597199997380000000000000)
      constant := (11353680718935385944837329400870208580820569796) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree086.table
  base := (2009819319061371268950245957297639575237/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-59916989060316416793317006987460000000000000)
      constant := (1468071420289378708740412423545689834002782184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229855399764933505227/50000000000000000000)
  centralHi := (91942159905973402091/20000000000000000000)
  directionLo := (7225110526148016629/1562500000000000000)
  directionHi := (462407073673473064257/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree087.table
  base := (17366931702567770479711414343372469838633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-944101204336777494366128582182020000000000000)
      constant := (23222305417521048795559572312187041407182509217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree087.table
  base := (17366928234937549760577690028399689423501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-6730787277793079848992041645130000000000000)
      constant := (166818392788346146684497463362742874843303581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7225110526148016629/1562500000000000000)
  centralHi := (462407073673473064257/100000000000000000000)
  directionLo := (465087716847198532521/100000000000000000000)
  directionHi := (232543858423599266261/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree088.table
  base := (18685535155003132209838749491742279590877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-954384545809242679471062764369280000000000000)
      constant := (23743073546570986625413033381428877359035950773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree088.table
  base := (18685532210303315286638748350104191145013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-61237181939959020488539742624880000000000000)
      constant := (1535036184020590346884110639239545955344714477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465087716847198532521/100000000000000000000)
  centralHi := (232543858423599266261/50000000000000000000)
  directionLo := (467752997789447725911/100000000000000000000)
  directionHi := (58469124723680965739/12500000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree089.table
  base := (10017184410552130797420743587464021369031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-482333943640853932287998473278270000000000000)
      constant := (12134832911528080304998727487635040580654035919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree089.table
  base := (5008591580199128595403852890747203427053/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-61897278379780322336151110443590000000000000)
      constant := (1569083366950773601449497096527161345193286548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (467752997789447725911/100000000000000000000)
  centralHi := (58469124723680965739/12500000000000000000)
  directionLo := (94080635525041020129/20000000000000000000)
  directionHi := (235201588812602550323/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree090.table
  base := (4282686510326800727703281167363884323029/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-974951228754173049680931128743800000000000000)
      constant := (24802082245267954561761306410114745558071795105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree090.table
  base := (21413430428920746075871853035157800267893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (551)
      previous := (0)
      next := (475)
      square := (7587315400244848823119170330000000000000)
      linear := (-772313269377797829429166398300000000000000)
      constant := (19796383750437409969750271907566420202411037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94080635525041020129/20000000000000000000)
  centralHi := (235201588812602550323/50000000000000000000)
  directionLo := (236519255082311127307/50000000000000000000)
  directionHi := (94607702032924450923/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree091.table
  base := (22822726216248302107617760317816689683821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-985234570226638234785865310931060000000000000)
      constant := (25340322811714059380890157149630613280190066629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree091.table
  base := (22822724414326967123799984881605760764973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-63217471259422926031373846081010000000000000)
      constant := (1638307334436825712658887127128533099597665317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236519255082311127307/50000000000000000000)
  centralHi := (94607702032924450923/20000000000000000000)
  directionLo := (95131848437343127989/20000000000000000000)
  directionHi := (237829621093357819973/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree092.table
  base := (485244994011871386846347158448309420873/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-497758955849551709945399746559160000000000000)
      constant := (12942193760542620421133317107823427363989374425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree092.table
  base := (23693601729657051602840820995279987241/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-63877567699244227878985213899720000000000000)
      constant := (1673484118827798122754140206506212529355457536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95131848437343127989/20000000000000000000)
  centralHi := (237829621093357819973/50000000000000000000)
  directionLo := (478265613709072518591/100000000000000000000)
  directionHi := (7472900214204258103/1562500000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree093.table
  base := (25732002903864262766672334933643653210933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1005801253171568604995733675305580000000000000)
      constant := (26434276372227376288938767761467856185611971917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree093.table
  base := (25732001605880335024476559817374784170459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-7170851571007281080732953524270000000000000)
      constant := (189893048543348649344319097366349857517807179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478265613709072518591/100000000000000000000)
  centralHi := (7472900214204258103/1562500000000000000)
  directionLo := (480857858244399440013/100000000000000000000)
  directionHi := (240428929122199720007/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree094.table
  base := (13615992868373626253364153673349594937637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-508042297322016895050333928746420000000000000)
      constant := (13494994682058959848489827022311319512441006013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree094.table
  base := (5446396927061614946624381390382956324869/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-65197760578886831574207949537140000000000000)
      constant := (1744967288563226022621690365899075875804147505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (480857858244399440013/100000000000000000000)
  centralHi := (240428929122199720007/50000000000000000000)
  directionLo := (24171810152234467997/5000000000000000000)
  directionHi := (483436203044689359941/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree095.table
  base := (28762198119691293891364572963229301274163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1026367936116498975205602039680100000000000000)
      constant := (27551526495846088866149632145642262270287892187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree095.table
  base := (5752439437028154751040032372637941274621/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-65857857018708133421819317355850000000000000)
      constant := (1781273673792889745254014957617327795945993545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24171810152234467997/5000000000000000000)
  centralHi := (483436203044689359941/100000000000000000000)
  directionLo := (243000434666864993983/50000000000000000000)
  directionHi := (486000869333729987967/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree096.table
  base := (30322639981449773149050670594759570286869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1036651277588964160310536221867360000000000000)
      constant := (28118887766596181315378449814379882320214363181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree096.table
  base := (1212905567543545763582526414069721354169/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-7390883717614381696603409463840000000000000)
      constant := (201995176947826584060334293305611185742192225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243000434666864993983/50000000000000000000)
  centralHi := (486000869333729987967/100000000000000000000)
  directionLo := (12213801813215665899/2500000000000000000)
  directionHi := (488552072528626635961/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree097.table
  base := (7978327814463293514256094790359155742409/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-523467309530714672707735202027310000000000000)
      constant := (14346036587816760126715851190846128948189681282) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree097.table
  base := (6382662117054451971634099870056282943229/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-67178049898350737117042052993270000000000000)
      constant := (1855016044731857955023579958462537651328069705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12213801813215665899/2500000000000000000)
  centralHi := (488552072528626635961/100000000000000000000)
  directionLo := (491090022450967366803/100000000000000000000)
  directionHi := (122772505612741841701/25000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree098.table
  base := (4191776486346833682042554642711958142261/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-528608980266947265260202293120940000000000000)
      constant := (14635541361146305818083312774209496835082984756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree098.table
  base := (33534211320287368958225416876502024295403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-67838146338172038964653420811980000000000000)
      constant := (1892452030357120640912790074268339975711348787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (491090022450967366803/100000000000000000000)
  centralHi := (122772505612741841701/25000000000000000000)
  directionLo := (246807461764108138887/50000000000000000000)
  directionHi := (19744596941128651111/4000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree099.table
  base := (35185341827258085963011091419899374124123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1067501302006359715625338768429140000000000000)
      constant := (29855916405967160234509943529139157934347084227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree099.table
  base := (17592670671708701178566736659419864186209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (551)
      previous := (0)
      next := (475)
      square := (7587315400244848823119170330000000000000)
      linear := (-845657318246831368052651711490000000000000)
      constant := (23830426535427400436862686922112057555351762) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (246807461764108138887/50000000000000000000)
  centralHi := (19744596941128651111/4000000000000000000)
  directionLo := (124031743746470497877/25000000000000000000)
  directionHi := (496126974985881991509/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree100.table
  base := (7373340203756480120955795101346520559743/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1077784643478824900730272950616400000000000000)
      constant := (30446574226101648856452281734916581569442488035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree100.table
  base := (184333503042349974353138058111837487787/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-69158339217814642659876156449400000000000000)
      constant := (1968453601735680104223511973137705905719344600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124031743746470497877/25000000000000000000)
  centralHi := (496126974985881991509/100000000000000000000)
  directionLo := (249313185515486297743/50000000000000000000)
  directionHi := (498626371030972595487/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree101.table
  base := (38578289420641053802823465545743630498719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1088067984951290085835207132803660000000000000)
      constant := (31043056182184232101375722843218748825579833831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree101.table
  base := (38578289072717643176891742402777765337659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-69818435657635944507487524268110000000000000)
      constant := (2007019187424154297504089142447067490931153411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249313185515486297743/50000000000000000000)
  centralHi := (498626371030972595487/100000000000000000000)
  directionLo := (250556650513607560001/50000000000000000000)
  directionHi := (501113301027215120003/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree102.table
  base := (20160053495708914767296041500510130360671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-549175663211877635470070657495460000000000000)
      constant := (15822681136870367856019031763644000482499322279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree102.table
  base := (32256085357140659736787060759393901891/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-7830948010828582928344321342980000000000000)
      constant := (227329034045119505360956266852218632566463750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250556650513607560001/50000000000000000000)
  centralHi := (501113301027215120003/100000000000000000000)
  directionLo := (503587949662486949497/100000000000000000000)
  directionHi := (251793974831243474749/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree103.table
  base := (42092153692543966040498775442311394867651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1108634667896220456045075497178180000000000000)
      constant := (32253492500329585935053803072850393159839736299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree103.table
  base := (21046076721227291752934247140081295700729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-71138628537278548202710259905530000000000000)
      constant := (2085279958654368828644574967547821029131662882) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (503587949662486949497/100000000000000000000)
  centralHi := (251793974831243474749/50000000000000000000)
  directionLo := (253025248554439059353/50000000000000000000)
  directionHi := (506050497108878118707/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree104.table
  base := (10973607371980901902073073161015446217793/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-559459004684342820575004839682720000000000000)
      constant := (16433723430768760659186688458036771687495024114) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree104.table
  base := (43894429275921840802635310124248326056261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-71798724977099850050321627724240000000000000)
      constant := (2124975144143605103189269131309857029695014269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253025248554439059353/50000000000000000000)
  centralHi := (506050497108878118707/100000000000000000000)
  directionLo := (50850111917577706807/10000000000000000000)
  directionHi := (508501119175777068071/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree105.table
  base := (4572693434361676416554059388713983000369/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-564600675420575413127471930776350000000000000)
      constant := (16743612678487981457828755311382056956856123405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree105.table
  base := (45726934163918574169561184636643914732869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-8050980157435683544214777282550000000000000)
      constant := (240560762538865966062124751243130657093362389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50850111917577706807/10000000000000000000)
  centralHi := (508501119175777068071/100000000000000000000)
  directionLo := (127734996864086988387/25000000000000000000)
  directionHi := (510939987456347953549/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree106.table
  base := (23794834113785336561519639892714615001813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-569742346156808005679939021869980000000000000)
      constant := (17056413993138969324011201512175229627155757037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree106.table
  base := (5948708509408449469123646927218684442913/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-73118917856742453745544363361660000000000000)
      constant := (2205495114750206432808819946173469367671068616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127734996864086988387/25000000000000000000)
  centralHi := (510939987456347953549/100000000000000000000)
  directionLo := (513367269467744871327/100000000000000000000)
  directionHi := (16042727170867027229/3125000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree107.table
  base := (24741315554695954820284885278382831570347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 535000000000000000000000000000000000000000
      center := (3249)
      previous := (0)
      next := (2850)
      square := (45102374879233268004097290295000000000000)
      linear := (-5372747821430285964788842177230000000000000)
      constant := (162356330603249879413422390658441962978027129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree107.table
  base := (773166109067484172587470786331634354771/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-73779014296563755593155731180370000000000000)
      constant := (2246319899823228527346523566353971232456195776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (513367269467744871327/100000000000000000000)
  centralHi := (16042727170867027229/3125000000000000000)
  directionLo := (515783128785387228131/100000000000000000000)
  directionHi := (128945782196346807033/25000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree108.table
  base := (10281164592030562267837270829934990570779/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1160051375258546381569746408114480000000000000)
      constant := (35381505645097376748430926895155148535224243855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree108.table
  base := (25702911425388181848542829677592786476383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (551)
      previous := (0)
      next := (475)
      square := (7587315400244848823119170330000000000000)
      linear := (-919001367115864906676137024680000000000000)
      constant := (28241002691953480419516829375516670156574894) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (515783128785387228131/100000000000000000000)
  centralHi := (128945782196346807033/25000000000000000000)
  directionLo := (64773465646450104483/12500000000000000000)
  directionHi := (103637545034320167173/20000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree109.table
  base := (13339810938056702129567297694602041409231/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-585167358365505783337340295150870000000000000)
      constant := (18012290336983674856697806180694562544188571438) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree109.table
  base := (10671848731909815816667264280688665888991/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-75099207176206359288378466817790000000000000)
      constant := (2329099069405467511322858628797152687165372195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64773465646450104483/12500000000000000000)
  centralHi := (103637545034320167173/20000000000000000000)
  directionLo := (520581214698911018999/100000000000000000000)
  directionHi := (520581214698911019/100000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree110.table
  base := (55342893459148112284482278187930872104319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1180618058203476751779614772489000000000000000)
      constant := (36673479835402386272326644109790620554722348231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree110.table
  base := (27671446690313130156005076394817313589331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-75759303616027661135989834636500000000000000)
      constant := (2371053453875973393033994080971893643213244598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (520581214698911018999/100000000000000000000)
  centralHi := (520581214698911019/100000000000000000)
  directionLo := (522963749868256988593/100000000000000000000)
  directionHi := (261481874934128494297/50000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree111.table
  base := (57356772055491936820530225747913537816409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1190901399675941936884548954676260000000000000)
      constant := (37328203129111398052401807213032992094460066641) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree111.table
  base := (28678385994484614467145493226004391387363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-8491044450649884775955689161690000000000000)
      constant := (268153819049055151391675838905895211404752806) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (522963749868256988593/100000000000000000000)
  centralHi := (261481874934128494297/50000000000000000000)
  directionLo := (4202683837779046889/800000000000000000)
  directionHi := (262667739861190430563/50000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree112.table
  base := (1856277484899126259068608643823093912471/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-600592370574203560994741568431760000000000000)
      constant := (18994375277407021035419123431335849635262087664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree112.table
  base := (14850219865104852811069544658137491433887/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-77079496495670264831212570273920000000000000)
      constant := (2456091822084424819564522467041048925021214492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4202683837779046889/800000000000000000)
  centralHi := (262667739861190430563/50000000000000000000)
  directionLo := (263848274977314947571/50000000000000000000)
  directionHi := (527696549954629895143/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree113.table
  base := (3842200988709555003499101359319002253057/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-605734041310436153547208659525390000000000000)
      constant := (19327561056119857499989656234020831054361996744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree113.table
  base := (61475215771619306750139542086498421377697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-77739592935491566678823938092630000000000000)
      constant := (2499175805787731146293768167134439849184341113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263848274977314947571/50000000000000000000)
  centralHi := (527696549954629895143/100000000000000000000)
  directionLo := (66255887876674587831/12500000000000000000)
  directionHi := (530047103013396702649/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree114.table
  base := (31789890470187053744549758717168129721301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-610875712046668746099675750619020000000000000)
      constant := (19663658900563344354186929867152397917179175149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree114.table
  base := (31789890449972236257445570070763094616573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-8711076597256985391826145101260000000000000)
      constant := (282515146948324680423528706733233621327884826) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66255887876674587831/12500000000000000000)
  centralHi := (530047103013396702649/100000000000000000000)
  directionLo := (532387278202409291309/100000000000000000000)
  directionHi := (53238727820240929131/10000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree115.table
  base := (32857287428842744355683250422678575724487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-616017382782901338652142841712650000000000000)
      constant := (20002668810610682584175356371459372013469651663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree115.table
  base := (13142914964688961520495526321384855578801/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-79059785815134170374046673730050000000000000)
      constant := (2586473372309996128536108703707010298584729645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (532387278202409291309/100000000000000000000)
  centralHi := (53238727820240929131/10000000000000000000)
  directionLo := (33419825736066921221/6250000000000000000)
  directionHi := (534717211777070739537/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree116.table
  base := (13575919509958128215053108039058278475333/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1242318107038267862409219865612560000000000000)
      constant := (40689181572277632294978403200955571151320437585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree116.table
  base := (33939798760396847952005078684872410700287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-79719882254955472221658041548760000000000000)
      constant := (2630686955097406057323439218164823974801018446) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33419825736066921221/6250000000000000000)
  centralHi := (534717211777070739537/100000000000000000000)
  directionLo := (537037037037037037037/100000000000000000000)
  directionHi := (268518518518518518519/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree117.table
  base := (70074848995798230261074515497949247568917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1252601448510733047514154047799820000000000000)
      constant := (41378849654056305201630432556693390935416530733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree117.table
  base := (70074848971243795613338463312520531611229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (551)
      previous := (0)
      next := (475)
      square := (7587315400244848823119170330000000000000)
      linear := (-992345415984898445299622337870000000000000)
      constant := (33028111986197865407371189737295184784501061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537037037037037037037/100000000000000000000)
  centralHi := (268518518518518518519/50000000000000000000)
  directionLo := (539346884415211081071/100000000000000000000)
  directionHi := (33709180275950692567/6250000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree118.table
  base := (7230032917537948727928755504640153973969/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-631442394991599116309544114993540000000000000)
      constant := (21037170933162319906072974042479785614239855405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree118.table
  base := (14460065830917691332464985763196609124193/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-81040075134598075916880777186180000000000000)
      constant := (2720243719649128602657317829943821640257683485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (539346884415211081071/100000000000000000000)
  centralHi := (33709180275950692567/6250000000000000000)
  directionLo := (541646881563320950683/100000000000000000000)
  directionHi := (135411720390830237671/25000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree119.table
  base := (74556038068731084906064127346112477120791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1273168131455663417724022412174340000000000000)
      constant := (42775658208855907833139199540673171750555936159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree119.table
  base := (1491120761022558189269695177989456511669/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-81700171574419377764492145004890000000000000)
      constant := (2765586901384349439274917186292658189850335050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (541646881563320950683/100000000000000000000)
  centralHi := (135411720390830237671/25000000000000000000)
  directionLo := (13598428835856033479/2500000000000000000)
  directionHi := (543937153434241339161/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree120.table
  base := (15368395131308512921240892139171572930731/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1283451472928128602828956594361600000000000000)
      constant := (43482798681429023824840684737626876692419696095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree120.table
  base := (38420987820819752165940709587824338436427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-9151140890471186623567056980400000000000000)
      constant := (312367401785964032914393967133227542826701174) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13598428835856033479/2500000000000000000)
  centralHi := (543937153434241339161/100000000000000000000)
  directionLo := (273108911180604182117/50000000000000000000)
  directionHi := (109243564472241672847/20000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree121.table
  base := (39579070959983816198307984561401220344823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-646867407200296893966945388274430000000000000)
      constant := (22097881641914108283718988329508847571727878527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree121.table
  base := (79158141907351395156173948009933637878063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-83020364454061981459714880642310000000000000)
      constant := (2857402863703424497706035822631384122013107927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273108911180604182117/50000000000000000000)
  centralHi := (109243564472241672847/20000000000000000000)
  directionLo := (274244504067034927517/50000000000000000000)
  directionHi := (109697801626813971007/20000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree122.table
  base := (81504536840598749225493846821439184261807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1304018155873058973038824958736120000000000000)
      constant := (44914552015842738146326962083178377220613428343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree122.table
  base := (40752268414959578386458621391520072359249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-83680460893883283307326248461020000000000000)
      constant := (2903875644260220957760236061780206265499785042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274244504067034927517/50000000000000000000)
  centralHi := (109697801626813971007/20000000000000000000)
  directionLo := (110150165614541119321/20000000000000000000)
  directionHi := (275375414036352798303/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree123.table
  base := (3355246416017781261002498083389808523927/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1314301497345524158143759140923380000000000000)
      constant := (45639164877266605211040177688205217944761005575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree123.table
  base := (16776232078280981203057122446457653251627/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-9371173037078287239437512919970000000000000)
      constant := (327858328636776551062614499190557849566908935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110150165614541119321/20000000000000000000)
  centralHi := (275375414036352798303/50000000000000000000)
  directionLo := (553003397097744862067/100000000000000000000)
  directionHi := (138250849274436215517/25000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree124.table
  base := (86288012581909553358177764440334336790067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1324584838817989343248693323110640000000000000)
      constant := (46369601867898367730023261583709867821909477083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree124.table
  base := (3451520502970342561175706580016286119351/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-85000653773525887002548984098440000000000000)
      constant := (2997950804102934495631435935771876814525171975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553003397097744862067/100000000000000000000)
  centralHi := (138250849274436215517/25000000000000000000)
  directionLo := (555246827798701846849/100000000000000000000)
  directionHi := (11104936555974036937/2000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree125.table
  base := (88725093367776205306353153061900891847761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1334868180290454528353627505297900000000000000)
      constant := (47105862987540901293043960333361953310765015689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree125.table
  base := (44362546680650477126116033032219809472681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-85660750213347188850160351917150000000000000)
      constant := (3045553183363533946249520773812538982211168898) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555246827798701846849/100000000000000000000)
  centralHi := (11104936555974036937/2000000000000000000)
  directionLo := (111496246099928661853/20000000000000000000)
  directionHi := (278740615249821654633/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree126.table
  base := (11399050342648539857353832867149074280201/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-672575760881459856729280843742580000000000000)
      constant := (23923974118000609813411303055113099005736084996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree126.table
  base := (22798100683927119541233358872522037785657/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (551)
      previous := (0)
      next := (475)
      square := (7587315400244848823119170330000000000000)
      linear := (-1065689464853931983923107651060000000000000)
      constant := (38191754265438554420957141960140793360283652) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111496246099928661853/20000000000000000000)
  centralHi := (278740615249821654633/50000000000000000000)
  directionLo := (17490834791328024667/3125000000000000000)
  directionHi := (111941342664499357869/20000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree127.table
  base := (46844970342818155086213330226180237405503/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-677717431617692449281747934836210000000000000)
      constant := (24297928806545152252969294746528822538055603847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree127.table
  base := (93689940680999151033258811389716869908917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-86980943092989792545383087554570000000000000)
      constant := (3141887540501886014304199636796886098163600493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17490834791328024667/3125000000000000000)
  centralHi := (111941342664499357869/20000000000000000000)
  directionLo := (280961691124051098991/50000000000000000000)
  directionHi := (561923382248102197983/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree128.table
  base := (96217707184943635035653664718076664170897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1365718204707850083668430051859680000000000000)
      constant := (49349591118622950675714590313154379728092599753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree128.table
  base := (96217707181019813548812432130357953509359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-87641039532811094392994455373280000000000000)
      constant := (3190619518355847611733713677658550948108322711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280961691124051098991/50000000000000000000)
  centralHi := (561923382248102197983/100000000000000000000)
  directionLo := (35258208823444019841/6250000000000000000)
  directionHi := (564131341175104317457/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree129.table
  base := (98775702223254378827126554047982318216897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1376001546180315268773364234046940000000000000)
      constant := (50109148752417623769650370312329279561265253753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree129.table
  base := (49387851109967181808414458011949940113609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-9811237330292488471178424799110000000000000)
      constant := (359969781005651464662109628678418390298404658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35258208823444019841/6250000000000000000)
  centralHi := (564131341175104317457/100000000000000000000)
  directionLo := (7079133649709735131/1250000000000000000)
  directionHi := (566330691976778810481/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree130.table
  base := (2534098144625545804117934477901904858957/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-693142443826390226939149208117100000000000000)
      constant := (25437265257148164756014973299374478174603973860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree130.table
  base := (101363925782212876361814368865885280657123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-88961232412453698088217191010700000000000000)
      constant := (3289213072575611409745783529263480369599042667) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7079133649709735131/1250000000000000000)
  centralHi := (566330691976778810481/100000000000000000000)
  directionLo := (568521534555879677989/100000000000000000000)
  directionHi := (56852153455587967799/10000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree131.table
  base := (10398237785499792560266231158921161225559/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-698284114562622819491616299210730000000000000)
      constant := (25822868202042246377884384550913606874357124955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree131.table
  base := (5199118892631075023205156517436998602401/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-89621328852274999935828558829410000000000000)
      constant := (3339074648918986817482068024767473939623006580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (568521534555879677989/100000000000000000000)
  centralHi := (56852153455587967799/10000000000000000000)
  directionLo := (570703966897591716991/100000000000000000000)
  directionHi := (4458624741387435289/781250000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree132.table
  base := (5331552920911170791239187040387208322559/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-703425785298855412044083390304360000000000000)
      constant := (26211383210805422562069960178560891480849779910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree132.table
  base := (106631058416213035805528131090463857219003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-10031269476899589087048880738680000000000000)
      constant := (376590306452232544031299594559807572434739243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (570703966897591716991/100000000000000000000)
  centralHi := (4458624741387435289/781250000000000000)
  directionLo := (11457561702413347837/2000000000000000000)
  directionHi := (572878085120667391851/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree133.table
  base := (109309967460018731871223631496647803297089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1417134912070176009193100962795980000000000000)
      constant := (53205620566707320209223985718768890699948371961) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree133.table
  base := (27327491864579527900051489158920399312737/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-90941521731917603631051294466830000000000000)
      constant := (3439927400018235674841759498937894384395941092) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11457561702413347837/2000000000000000000)
  centralHi := (572878085120667391851/100000000000000000000)
  directionLo := (115008796705364725803/20000000000000000000)
  directionHi := (71880497940852953627/12500000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree134.table
  base := (560095524829877017504739887390579531513/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-713709126771320597149017572491620000000000000)
      constant := (26997149419604477717615683425019414505629233700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree134.table
  base := (1400238812056711201803247647449236136531/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-91601618171738905478662662285540000000000000)
      constant := (3490918574752917675850131284773969451482487920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115008796705364725803/20000000000000000000)
  centralHi := (71880497940852953627/12500000000000000000)
  directionLo := (115440350929694072319/20000000000000000000)
  directionHi := (144300438662117590399/25000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree135.table
  base := (57379235460974002616996004881080464242693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-718850797507553189701484663585250000000000000)
      constant := (27394400619476899912920973555382615235114592157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree135.table
  base := (57379235460365639697396278287140937479311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (551)
      previous := (0)
      next := (475)
      square := (7587315400244848823119170330000000000000)
      linear := (-1139033513722965522546592964250000000000000)
      constant := (43731929410664595272660983870231036874627598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115440350929694072319/20000000000000000000)
  centralHi := (144300438662117590399/25000000000000000000)
  directionLo := (289675744647419586187/50000000000000000000)
  directionHi := (4634811914358713379/800000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree136.table
  base := (58764032657023279636582382254403207083419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-723992468243785782253951754678880000000000000)
      constant := (27794563882891413512627843577972102317898064131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree136.table
  base := (117528065313017478084541997647257313055041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-92921811051381509173885397922960000000000000)
      constant := (3594030522540858020546150586149330581217124889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289675744647419586187/50000000000000000000)
  centralHi := (4634811914358713379/800000000000000000)
  directionLo := (290746638298288549453/50000000000000000000)
  directionHi := (581493276596577098907/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree137.table
  base := (58753851625307299149476615758776854749/4882812500000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-729134138980018374806418845772510000000000000)
      constant := (28197639209769926507996837852466854879061812224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree137.table
  base := (120327888127759020246981680802594734330459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-93581907491202811021496765741670000000000000)
      constant := (3646151295574054098168366177635074061326904611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290746638298288549453/50000000000000000000)
  centralHi := (581493276596577098907/100000000000000000000)
  directionLo := (23345088161954702409/4000000000000000000)
  directionHi := (291813602024433780113/50000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree138.table
  base := (30789484838074024723408620868633809725821/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-734275809716250967358885936866140000000000000)
      constant := (28603626600035729027679911721743436975101849258) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree138.table
  base := (61578969675780036039584685575108799737901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-10471333770113790318789792617820000000000000)
      constant := (410960955705961654123315730967897625557539962) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23345088161954702409/4000000000000000000)
  centralHi := (291813602024433780113/50000000000000000000)
  directionLo := (585753357553137430201/100000000000000000000)
  directionHi := (292876678776568715101/50000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree139.table
  base := (15752277371485186514810734472488150495413/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-739417480452483559911353027959770000000000000)
      constant := (29012526053613456209580637166505232340087933748) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree139.table
  base := (2520364379425181503686359089933809918671/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-94902100370845414716719501379090000000000000)
      constant := (3751522439870065611299318983130329871535557950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (585753357553137430201/100000000000000000000)
  centralHi := (292876678776568715101/50000000000000000000)
  directionLo := (73483977682175813417/12500000000000000000)
  directionHi := (587871821457406507337/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree140.table
  base := (2578174539488979656216302467119768073761/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-744559151188716152463820119053400000000000000)
      constant := (29424337570429052798859085614253355616912242225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree140.table
  base := (25781745394784533312449157459709867889709/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-95562196810666716564330869197800000000000000)
      constant := (3804772811113857849109665972749642468457989305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73483977682175813417/12500000000000000000)
  centralHi := (587871821457406507337/100000000000000000000)
  directionLo := (147495669648833251239/25000000000000000000)
  directionHi := (589982678595333004957/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree141.table
  base := (131829463347284888200081927494413118193837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1499401643849897490032574420294060000000000000)
      constant := (59678122300819478636990598250063465790201239813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree141.table
  base := (32957365836709964344728125703096481812759/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-10691365916720890934660248557390000000000000)
      constant := (428711079452862809964540791134785760107333916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147495669648833251239/25000000000000000000)
  centralHi := (589982678595333004957/100000000000000000000)
  directionLo := (74010751290500775053/12500000000000000000)
  directionHi := (23683440412960248017/4000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree142.table
  base := (3369510701947318252393352632985215632709/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-754842492661181337568754301240660000000000000)
      constant := (30256696793483979679087461727968014675577706820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree142.table
  base := (134780428077516449651457454928659339073719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-96882389690309320259553604835220000000000000)
      constant := (3912403151746679662683417014506762658184741151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74010751290500775053/12500000000000000000)
  centralHi := (23683440412960248017/4000000000000000000)
  directionLo := (18568184267516719643/3125000000000000000)
  directionHi := (594181896560535028577/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree143.table
  base := (137761621153987807846830633997304898851857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1519968326794827860242442784668580000000000000)
      constant := (61354488999162900223518523075701713786954910793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree143.table
  base := (137761621153669672620890469662831954501223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-97542486130130622107164972653930000000000000)
      constant := (3966783121117646828234011818795986994831391567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18568184267516719643/3125000000000000000)
  centralHi := (594181896560535028577/100000000000000000000)
  directionLo := (596270415817479175301/100000000000000000000)
  directionHi := (298135207908739587651/50000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree144.table
  base := (28154608512698396940042117249875631293777/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1530251668267293045347376966855840000000000000)
      constant := (62201408537266018645334457652946410513412264365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree144.table
  base := (35193260640805755706269980424567758086237/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (551)
      previous := (0)
      next := (475)
      square := (7587315400244848823119170330000000000000)
      linear := (-1212377562591999061170078277440000000000000)
      constant := (49648637323208185374182192323764439291104532) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (596270415817479175301/100000000000000000000)
  centralHi := (298135207908739587651/50000000000000000000)
  directionLo := (598351645237167114583/100000000000000000000)
  directionHi := (74793955654645889323/12500000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree145.table
  base := (14381469229452867199776049069200305278251/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-770267504869879115226155574521550000000000000)
      constant := (31527076100570669780037993026899496475653478495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree145.table
  base := (143814692294301293792257215832684062547063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-98862679009773225802387708291350000000000000)
      constant := (4076672657924671198389734986891089181596808927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (598351645237167114583/100000000000000000000)
  centralHi := (74793955654645889323/12500000000000000000)
  directionLo := (600425660624943529591/100000000000000000000)
  directionHi := (75053207578117941199/12500000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree146.table
  base := (36721642583854499376377584064122285983979/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-775409175606111707778622665615180000000000000)
      constant := (31956359995327570055268192810767012104461151142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree146.table
  base := (14688657033522578290228042022283671639333/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-99522775449594527649999076110060000000000000)
      constant := (4132182225343557603266860576480777966250737570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (600425660624943529591/100000000000000000000)
  centralHi := (75053207578117941199/12500000000000000000)
  directionLo := (37655783530086666193/6250000000000000000)
  directionHi := (602492536481386659089/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree147.table
  base := (74994338337336072874369161697518219412839/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-780550846342344300331089756708810000000000000)
      constant := (32388555952837948148672783236564371094057593711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree147.table
  base := (4687146146078427011042349188391392402799/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-11131430209935092166401160436530000000000000)
      constant := (465340925047572037103402917549052989108055008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37655783530086666193/6250000000000000000)
  centralHi := (602492536481386659089/100000000000000000000)
  directionLo := (151138086508383577127/25000000000000000000)
  directionHi := (604552346033534308509/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree148.table
  base := (76560505650495429790055010868798611328301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-785692517078576892883556847802440000000000000)
      constant := (32823663973037115738211848357638235301097718149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree148.table
  base := (30624202260170703672551221825534010006261/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-100842968329237131345221811747480000000000000)
      constant := (4244330958170206113359425237912191466472821345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151138086508383577127/25000000000000000000)
  centralHi := (604552346033534308509/100000000000000000000)
  directionLo := (121321032253031110983/20000000000000000000)
  directionHi := (151651290316288888729/25000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree149.table
  base := (31256714840651418673514399369502953425399/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1581668375629618970872047877792140000000000000)
      constant := (66523368111722866592329396577111926568836965755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree149.table
  base := (19535446775392625969049100685869209131581/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-101503064769058433192833179566190000000000000)
      constant := (4300970123561627131750429600188631727655380392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121321032253031110983/20000000000000000000)
  centralHi := (151651290316288888729/25000000000000000000)
  directionLo := (304325526473051775733/50000000000000000000)
  directionHi := (608651052946103551467/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree150.table
  base := (79738182685266404592552461859921496017963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-795975858551042077988491029989700000000000000)
      constant := (33702616201248286024423835403326741207909658387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree150.table
  base := (7973818268521734697496832306809732177529/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-11351462356542192782271616376100000000000000)
      constant := (484220646843826444042712420333281766127596980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304325526473051775733/50000000000000000000)
  centralHi := (608651052946103551467/100000000000000000000)
  directionLo := (12213801813215665899/2000000000000000000)
  directionHi := (610690090660783294951/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree151.table
  base := (1016871154950343176547652904363594859349/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-801117529287274670540958121083330000000000000)
      constant := (34146460409136060563994044411036468803574936080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree151.table
  base := (162699384791971985195612935759039735327899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-102823257648701036888055915203610000000000000)
      constant := (4415378052260792777868496033459282467054038371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12213801813215665899/2000000000000000000)
  centralHi := (610690090660783294951/100000000000000000000)
  directionLo := (612722342835766754963/100000000000000000000)
  directionHi := (153180585708941688741/25000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree152.table
  base := (82976316228615645286236851247177611985859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-806259200023507263093425212176960000000000000)
      constant := (34593216679464122438524605788669096479626099691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree152.table
  base := (33190526491432242080430847809432091225557/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-103483354088522338735667283022320000000000000)
      constant := (4473146815552970147980064391228099972517155265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (612722342835766754963/100000000000000000000)
  centralHi := (153180585708941688741/25000000000000000000)
  directionLo := (614747876766586370859/100000000000000000000)
  directionHi := (30737393838329318543/5000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree153.table
  base := (169236108355637036491876656542182848515237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1622801741519479711291784606541180000000000000)
      constant := (70085770024345588390754671870946821432650948413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree153.table
  base := (84618054177788906343161936325213903448213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (551)
      previous := (0)
      next := (475)
      square := (7587315400244848823119170330000000000000)
      linear := (-1285721611461032599793563590630000000000000)
      constant := (55941877919300871663595522396836350262067834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (614747876766586370859/100000000000000000000)
  centralHi := (30737393838329318543/5000000000000000000)
  directionLo := (308383379321868299423/50000000000000000000)
  directionHi := (616766758643736598847/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree154.table
  base := (172549812477010704198452876097750345516949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1633085082991944896396718788728440000000000000)
      constant := (70990930814406668421851770922331823705823549101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree154.table
  base := (172549812476960657087951915120223737384717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-104803546968164942430890018659740000000000000)
      constant := (4589813939984513780796050929470173104553458693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308383379321868299423/50000000000000000000)
  centralHi := (616766758643736598847/100000000000000000000)
  directionLo := (309389526788955966283/50000000000000000000)
  directionHi := (618779053577911932567/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree155.table
  base := (175893744811250737992066080385140473194579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1643368424464410081501652970915700000000000000)
      constant := (71901915728995832259129648452889723277604734971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree155.table
  base := (1099335905070052796422344672260556305009/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-105463643407986244278501386478450000000000000)
      constant := (4648712301109035831199676550633033787416249760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (309389526788955966283/50000000000000000000)
  centralHi := (618779053577911932567/100000000000000000000)
  directionLo := (38799051601531788919/6250000000000000000)
  directionHi := (124156965124901724541/20000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree156.table
  base := (35853581069682396464315797180574162471907/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1653651765936875266606587153102960000000000000)
      constant := (72818724767999217816683333703812047930704316215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree156.table
  base := (179267905348376247635826743206356515279831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-11791526649756394014012528255240000000000000)
      constant := (523109688314409655285282862324234877737666311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38799051601531788919/6250000000000000000)
  centralHi := (124156965124901724541/20000000000000000000)
  directionLo := (311392068903708090641/50000000000000000000)
  directionHi := (622784137807416181283/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree157.table
  base := (182672294078702297088518857193215556169281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1663935107409340451711521335290220000000000000)
      constant := (73741357931304714882525412326843294902582098169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree157.table
  base := (36534458815734420644901108533657024852037/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-106783836287628847973724122115870000000000000)
      constant := (4767638621139328645077759915133062355585674865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311392068903708090641/50000000000000000000)
  centralHi := (622784137807416181283/100000000000000000000)
  directionLo := (156194263035530917759/25000000000000000000)
  directionHi := (624777052142123671037/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree158.table
  base := (186106910992479270008801111883332644375001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1674218448881805636816455517477480000000000000)
      constant := (74669815218801927478415399938396795445449386449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree158.table
  base := (93053455496226879433671032392791711560131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-107443932727450149821335489934580000000000000)
      constant := (4827666580030931869597468561510860315454670998) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156194263035530917759/25000000000000000000)
  centralHi := (624777052142123671037/100000000000000000000)
  directionLo := (626763629658164746883/100000000000000000000)
  directionHi := (156690907414541186721/25000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree159.table
  base := (189571756080247022119963500365973421930619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1684501790354270821921389699664740000000000000)
      constant := (75604096630382137286112066242719159707683656931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree159.table
  base := (189571756080225468323469720202831865710483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-12011558796363494629882984194810000000000000)
      constant := (543119007944174908013008884045711881122549123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (626763629658164746883/100000000000000000000)
  centralHi := (156690907414541186721/25000000000000000000)
  directionLo := (39296495651307776999/6250000000000000000)
  directionHi := (125748786084184886397/20000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree160.table
  base := (193066829332653102780219849354459100894907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1694785131826736007026323881852000000000000000)
      constant := (76544202165938268098217601341851202246145790243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree160.table
  base := (96533414666317446586585904120710045030371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-108764125607092753516558225572000000000000000)
      constant := (4948852095532437697928620625039995245654280918) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39296495651307776999/6250000000000000000)
  centralHi := (125748786084184886397/20000000000000000000)
  directionLo := (630718013552829672819/100000000000000000000)
  directionHi := (31535900677641483641/5000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree161.table
  base := (196592130740485470736660373203997652691223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1705068473299201192131258064039260000000000000)
      constant := (77490131825364851254427441099945699125661812127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree161.table
  base := (49148032685117521761901403288351403028953/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-109424222046914055364169593390710000000000000)
      constant := (5010009652128806938129204227616375191232426948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (630718013552829672819/100000000000000000000)
  centralHi := (31535900677641483641/5000000000000000000)
  directionLo := (158171484313486205883/25000000000000000000)
  directionHi := (632685937253944823533/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree162.table
  base := (25018457536833694755872907537579599969609/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-857675907385833188618096123113260000000000000)
      constant := (39220942804278996013185086037917255360208213764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree162.table
  base := (50036915073664140556315757514374889696611/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (551)
      previous := (0)
      next := (475)
      square := (7587315400244848823119170330000000000000)
      linear := (-1359065660330066138417048903820000000000000)
      constant := (62611651126914402360121621675087496029077996) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158171484313486205883/25000000000000000000)
  centralHi := (632685937253944823533/100000000000000000000)
  directionLo := (317323879410996178569/50000000000000000000)
  directionHi := (634647758821992357139/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree163.table
  base := (101866708993132706912752758699564129520293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-862817578122065781170563214206890000000000000)
      constant := (39699731757707668458177804839926394718877834557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree163.table
  base := (101866708993127217820369050128393250189181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-110744414926556659059392329028130000000000000)
      constant := (5133454362979699482295881065347079858775825898) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (317323879410996178569/50000000000000000000)
  centralHi := (634647758821992357139/100000000000000000000)
  directionLo := (636603534671818288079/100000000000000000000)
  directionHi := (7957544183397728601/1250000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree164.table
  base := (207349403806464924952701333847657658033589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1735918497716596747446060610601040000000000000)
      constant := (80362865545836041837278302905847912526826560461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree164.table
  base := (103674701903227825754196808584195270540713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-111404511366377960907003696846840000000000000)
      constant := (5195741517221284538839563833012436704448359554) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (636603534671818288079/100000000000000000000)
  centralHi := (7957544183397728601/1250000000000000000)
  directionLo := (638553320354321014717/100000000000000000000)
  directionHi := (319276660177160507359/50000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree165.table
  base := (10549780887329455552023327538559979820221/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (347643)
      previous := (0)
      next := (304950)
      square := (4825954112077959676438410061565000000000000)
      linear := (-873100919594530966275497396394150000000000000)
      constant := (40666045849860370571337423619429857089617102290) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree165.table
  base := (52748904436645319476687004226186606512877/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-12451623089577695861623896073950000000000000)
      constant := (584267244888721646603348844289346960510172148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (638553320354321014717/100000000000000000000)
  centralHi := (319276660177160507359/50000000000000000000)
  directionLo := (640497170574861550013/100000000000000000000)
  directionHi := (320248585287430775007/50000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree166.table
  base := (214672059798085491084769684340801388085371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1756485180661527117655928974975560000000000000)
      constant := (82307141976971517477530086220530515092189412579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree166.table
  base := (21467205979807887480063319593253023442913/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-112724704246020564602226432484260000000000000)
      constant := (5321445423305095595281970814646344540898835770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (640497170574861550013/100000000000000000000)
  centralHi := (320248585287430775007/50000000000000000000)
  directionLo := (321217569605586200899/50000000000000000000)
  directionHi := (642435139211172401799/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree167.table
  base := (218378729952525519364992055222233938026263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1766768522133992302760863157162820000000000000)
      constant := (83288016377491872421888656591162726356462685087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree167.table
  base := (109189364976259965549422448436355350544359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-113384800685841866449837800302970000000000000)
      constant := (5384862175134942481809569577509788601093675422) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (321217569605586200899/50000000000000000000)
  centralHi := (642435139211172401799/100000000000000000000)
  directionLo := (128873455866156337837/20000000000000000000)
  directionHi := (322183639665390844593/50000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree168.table
  base := (222115628201602088266576798157655802176491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1777051863606457487865797339350080000000000000)
      constant := (84274714901186697900671496800419321279118645459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree168.table
  base := (222115628201597368456421926417956365622743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (4959)
      previous := (0)
      next := (4275)
      square := (68285838602203639408072532970000000000000)
      linear := (-12671655236184796477494352013520000000000000)
      constant := (605406162164664402099939908585934465615442183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell211.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128873455866156337837/20000000000000000000)
  centralHi := (322183639665390844593/50000000000000000000)
  directionLo := (161573410801992109247/25000000000000000000)
  directionHi := (646293643207968436989/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree169.table
  base := (225882754537127095811809944851369908458891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (695286)
      previous := (0)
      next := (609900)
      square := (9651908224155919352876820123130000000000000)
      linear := (-1787335205078922672970731521537340000000000000)
      constant := (85267237547962248334335759625282864081945843059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree169.table
  base := (112941377268561554816948187628640289901037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (44631)
      previous := (0)
      next := (38475)
      square := (614572547419832754672652796730000000000000)
      linear := (-114704993565484470145060535940390000000000000)
      constant := (5512825276340237898244067508049500042675711946) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell211.Kernel169
