import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell093.Parameters
import ForestUnimodality.BinomialMassData.Q10996_21321.Batch000_049
import ForestUnimodality.BinomialMassData.Q10996_21321.Batch050_099
import ForestUnimodality.BinomialMassData.Q10996_21321.Batch100_149
import ForestUnimodality.BinomialMassData.Q10996_21321.Batch150_199
import ForestUnimodality.BinomialMassData.Q7339_14214.Batch000_049
import ForestUnimodality.BinomialMassData.Q7339_14214.Batch050_099
import ForestUnimodality.BinomialMassData.Q7339_14214.Batch100_149
import ForestUnimodality.BinomialMassData.Q7339_14214.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree000.table
  base := (749300743928159810780442741/10000000000000000000000000)
  polynomial :=
    { denominator := 400000000000000000000000000000000000000
      center := (6)
      previous := (3)
      next := (3)
      square := (29120511017489453253759279600000000000)
      linear := (-1146268143878755550735260000000000000)
      constant := (29972029757126392431217709640000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree000.table
  base := (749300743928159810780442741/10000000000000000000000000)
  polynomial :=
    { denominator := 400000000000000000000000000000000000000
      center := (6)
      previous := (3)
      next := (3)
      square := (29120511017489453253759279600000000000)
      linear := (-1146268143878755550735260000000000000)
      constant := (29972029757126392431217709640000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree001.table
  base := (102341310814979463795063770570304567273269/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-39376206840957013255867260394939020000000000000)
      constant := (20687339980558843836288510153341469580624998475124) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree001.table
  base := (408979921302608154539792374526399076747501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-13139774465860761192530369242765590000000000000)
      constant := (6889300226263016490991139119733277089374995878983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49973352339153401089/100000000000000000000)
  directionHi := (4997335233915340109/10000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree002.table
  base := (4747348184411499969225213245910054062133/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20203779600000000000000000000000000000000000000
      center := (303056694)
      previous := (151528347)
      next := (151528347)
      square := (1470860966091821647158638391232940400000000000)
      linear := (-3092199174922992394796051304123381600000000000)
      constant := (481196499132410364966071776029599670077099189434) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree002.table
  base := (14811171471546143880629995569274847975117/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-25797070828775116837782992423266680000000000000)
      constant := (4003457294637114999846407166352728234170268696176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49973352339153401089/100000000000000000000)
  centralHi := (4997335233915340109/10000000000000000000)
  directionLo := (70672992635279973749/100000000000000000000)
  directionHi := (56538394108223979/80000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree003.table
  base := (924557750454482224477046371484787709573/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 33672966000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (2451434943486369411931063985388234000000000000)
      linear := (-7682250127012840432262353654082004000000000000)
      constant := (504139291991857692443847250949210672986712056288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree003.table
  base := (9226731891775139637138662739513514742331/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-12818122397229824161011871867922590000000000000)
      constant := (838562451762078946895020062689675950057361396656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70672992635279973749/100000000000000000000)
  centralHi := (56538394108223979/80000000000000000)
  directionLo := (86556385275954691481/100000000000000000000)
  directionHi := (43278192637977345741/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree004.table
  base := (99466224273311867338477248586925711540063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-153162524437310403097969327019375580000000000000)
      constant := (5183459920288953269637363199136322453821523555287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree004.table
  base := (1550785706456270246298024794770900679971/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-51111663554603828128288238784268860000000000000)
      constant := (1724304113963296483876016440755797244353291647552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86556385275954691481/100000000000000000000)
  centralHi := (43278192637977345741/50000000000000000000)
  directionLo := (99946704678306802179/100000000000000000000)
  directionHi := (4997335233915340109/5000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree005.table
  base := (35830261314507153429911842173662021905917/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-191091296969428199712003349227521100000000000000)
      constant := (3867781237017071151502865543711936077387595019466) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree005.table
  base := (35753866872451589854988499368274118950887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-63768959917518183773540861964769950000000000000)
      constant := (1286874810757530473103812645049900448613173620842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99946704678306802179/100000000000000000000)
  centralHi := (4997335233915340109/5000000000000000000)
  directionLo := (111743812893895130061/100000000000000000000)
  directionHi := (55871906446947565031/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree006.table
  base := (54526446346416111832936289970271269640843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-76340023167181998775345790478555540000000000000)
      constant := (1036893897073895934313441057323143856696469275169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree006.table
  base := (54415610463585310211772199733029749554353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-25475418760144179806264495048423680000000000000)
      constant := (345098833476238053068553676696449262288707286833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111743812893895130061/100000000000000000000)
  centralHi := (55871906446947565031/50000000000000000000)
  directionLo := (122409213967245995979/100000000000000000000)
  directionHi := (6120460698362299799/5000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree007.table
  base := (1347332396656020637603076203490463091379/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-266948842033663792940071393643812140000000000000)
      constant := (2662171900419646195144743095625149600012478085472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree007.table
  base := (8606117077652330844913120998299642272581/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33672966000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (2451434943486369411931063985388234000000000000)
      linear := (-17816710528669379012809221665154426000000000000)
      constant := (177268178357717174720121800102880284528391372623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122409213967245995979/100000000000000000000)
  centralHi := (6120460698362299799/5000000000000000000)
  directionLo := (1322170624696078359/1000000000000000000)
  directionHi := (132217062469607835901/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree008.table
  base := (17467556542739599578945935397196007840983/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-304877614565781589554105415851957660000000000000)
      constant := (2396484317329545012103703616699389642095461896734) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree008.table
  base := (34868169381004784254156892715288894587031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-101740849006261250709298731506273220000000000000)
      constant := (798177925702745828048820239800986193803339451973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1322170624696078359/1000000000000000000)
  centralHi := (132217062469607835901/100000000000000000000)
  directionLo := (70672992635279973749/50000000000000000000)
  directionHi := (141345985270559947499/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree009.table
  base := (3588212205418405207986275461045929729531/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-38089598566433265129793270895567020000000000000)
      constant := (249872982631766952810129845625909728294515411928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree009.table
  base := (14325024549633971188383763393223621547431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-38132715123058535451517118228924770000000000000)
      constant := (249761767103577452020494042944758073754503816782) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70672992635279973749/50000000000000000000)
  centralHi := (141345985270559947499/100000000000000000000)
  directionLo := (149920057017460203269/100000000000000000000)
  directionHi := (14992005701746020327/10000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree010.table
  base := (1483913574666131923427203924622498232691/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-380735159630017182782173460268248700000000000000)
      constant := (2184752473333114040250643386953754699787139156144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree010.table
  base := (23694878401293531822279731548313428077807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-127055441732089961999803977867275400000000000000)
      constant := (728191545879728089497651829773098460503720232781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149920057017460203269/100000000000000000000)
  centralHi := (14992005701746020327/10000000000000000000)
  directionLo := (158029615705828023263/100000000000000000000)
  directionHi := (4938425490807125727/3125000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree011.table
  base := (19662818145596003309895073923499874705183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-418663932162134979396207482476394220000000000000)
      constant := (2184823380310073380825857567859669782927830774167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree011.table
  base := (19621029278536249645349643539136670132799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-139712738095004317645056601047776490000000000000)
      constant := (728471385931536180588197456289370763867478105917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158029615705828023263/100000000000000000000)
  centralHi := (4938425490807125727/3125000000000000000)
  directionLo := (41435714806300294887/25000000000000000000)
  directionHi := (165742859225201179549/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree012.table
  base := (16237803132297982840310818506770334508639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-152197568231417592003413834894846580000000000000)
      constant := (745842762890037055492725157826104601859013876637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree012.table
  base := (4050201027819048967525052931469344498587/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-50790011485972891096769741409425860000000000000)
      constant := (248763731454200689542521542858395871562138066028) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41435714806300294887/25000000000000000000)
  centralHi := (165742859225201179549/100000000000000000000)
  directionLo := (86556385275954691481/50000000000000000000)
  directionHi := (173112770551909382963/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree013.table
  base := (13321252546747807219013287912763693122163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-494521477226370572624275526892685260000000000000)
      constant := (2335476675634431023308554410991445646805542818187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree013.table
  base := (13288316896363179628297022473091677959101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-165027330820833028935561847408778670000000000000)
      constant := (779194763960949618615969401442430035899878681783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86556385275954691481/50000000000000000000)
  centralHi := (173112770551909382963/100000000000000000000)
  directionLo := (90090742132822939073/50000000000000000000)
  directionHi := (180181484265645878147/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree014.table
  base := (10812684894228825167367825416900123356253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-532450249758488369238309549100830780000000000000)
      constant := (2473593276270198484108012396936393478756369734597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree014.table
  base := (10783315641614849374884151776339047303363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-177684627183747384580814470589279760000000000000)
      constant := (825494203764484535865053976341043242159266992329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90090742132822939073/50000000000000000000)
  centralHi := (180181484265645878147/100000000000000000000)
  directionLo := (93491581460825072863/50000000000000000000)
  directionHi := (186983162921650145727/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree015.table
  base := (2159702154838489810308068858242548939183/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-190126340763535388617447857102992100000000000000)
      constant := (882725391499486428484200291660482340364890453556) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree015.table
  base := (344505165895442556185086602489156785419/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2244864400000000000000000000000000000000000000
      center := (33672966)
      previous := (16836483)
      next := (16836483)
      square := (163428996232424627462070932359215600000000000)
      linear := (-2537892313955489869680894583597078000000000000)
      constant := (11786100908190557259203857127486996134013880459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93491581460825072863/50000000000000000000)
  centralHi := (186983162921650145727/100000000000000000000)
  directionLo := (193545961363696583243/100000000000000000000)
  directionHi := (48386490340924145811/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree016.table
  base := (210738477128748503921052283533872415909/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-608307794822723962466377593517121820000000000000)
      constant := (2856397222319351056149734426902935954043597572512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree016.table
  base := (3360164658721467989387644313455283713987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-202999219909576095871319716950281940000000000000)
      constant := (953643224568907187822530983402144631021437975442) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193545961363696583243/100000000000000000000)
  centralHi := (48386490340924145811/25000000000000000000)
  directionLo := (99946704678306802179/50000000000000000000)
  directionHi := (199893409356613604359/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree017.table
  base := (5082962515978118362252929664657397956419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-646236567354841759080411615725267340000000000000)
      constant := (3096024390788788520049647953186506584552449703131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree017.table
  base := (1012452555842689214797866862698210204339/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33672966000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (2451434943486369411931063985388234000000000000)
      linear := (-43131303254498090303314468026156606000000000000)
      constant := (206761557124325848606282145645114738735780099737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99946704678306802179/50000000000000000000)
  centralHi := (199893409356613604359/100000000000000000000)
  directionLo := (206045410160536864053/100000000000000000000)
  directionHi := (103022705080268432027/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree018.table
  base := (3621169281156540669914850234083276859127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-76018371098551061743827293103712540000000000000)
      constant := (373917541397811132398039971969742397140995043447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree018.table
  base := (144112830677058829747005748907479935201/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2244864400000000000000000000000000000000000000
      center := (33672966)
      previous := (16836483)
      next := (16836483)
      square := (163428996232424627462070932359215600000000000)
      linear := (-3044184168472064095490999510817121600000000000)
      constant := (14984689665238686110232594176572935900617579361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206045410160536864053/100000000000000000000)
  centralHi := (103022705080268432027/50000000000000000000)
  directionLo := (212018977905839921247/100000000000000000000)
  directionHi := (6625593059557497539/3125000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree019.table
  base := (2329122986748518574457981543868814798873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-722094112419077352308479660141558380000000000000)
      constant := (3662626399324174505398017582301436523774121050977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree019.table
  base := (2312893646084924762371363825266520506703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-240971108998319162807077586491785210000000000000)
      constant := (1223284938516377444582601251020672925480256445549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212018977905839921247/100000000000000000000)
  centralHi := (6625593059557497539/3125000000000000000)
  directionLo := (217828792716321607451/100000000000000000000)
  directionHi := (54457198179080401863/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree020.table
  base := (36962731585314010494265392197179265803/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-760022884951195148922513682349703900000000000000)
      constant := (3986916924878917367811957107163173570237890321504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree020.table
  base := (292120522231069545072616311286755129749/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-253628405361233518452330209672286300000000000000)
      constant := (1331703362218138265474292199606266643468727331068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217828792716321607451/100000000000000000000)
  centralHi := (54457198179080401863/25000000000000000000)
  directionLo := (223487625787790260123/100000000000000000000)
  directionHi := (55871906446947565031/25000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree021.table
  base := (10144681491270703973238449102686809779/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-265983885827770981845515901519283140000000000000)
      constant := (1445707974950163589550404956613728747634693876112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree021.table
  base := (7484731793041714061610626781872826709/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (168364830)
      previous := (84182415)
      next := (84182415)
      square := (817144981162123137310354661796078000000000000)
      linear := (-17752380114943191606505522190185826000000000000)
      constant := (96584806251803854940203754687036014240064032596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223487625787790260123/100000000000000000000)
  centralHi := (55871906446947565031/25000000000000000000)
  directionLo := (1145033349124344749/500000000000000000)
  directionHi := (229006669824868949801/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree022.table
  base := (-748912914189788011017081120073251307307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-835880430015430742150581726765994940000000000000)
      constant := (4712411044572136631605289592555557076829393756157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree022.table
  base := (-95001400964939300543959956500108476341/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-278942998087062229742835456033288480000000000000)
      constant := (1574212615763788108497670889165305503119430810376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1145033349124344749/500000000000000000)
  centralHi := (229006669824868949801/100000000000000000000)
  directionLo := (117197899691387080223/50000000000000000000)
  directionHi := (234395799382774160447/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree023.table
  base := (-391169882101067735217786889718891632589/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (14322150)
      previous := (7161075)
      next := (7161075)
      square := (69511387811522762153054744387190000000000000)
      linear := (-1651813237329959430556929582181740000000000000)
      constant := (9663669333880974082892069168318762032115078764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree023.table
  base := (-1574423352730347499116613829440924927839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318270000000000000000000000000000000000000000
      center := (4774050)
      previous := (2387025)
      next := (2387025)
      square := (23170462603840920717684914795730000000000000)
      linear := (-551229290075570104703380111935330000000000000)
      constant := (3228341754727083404295182999885866182321668147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117197899691387080223/50000000000000000000)
  centralHi := (234395799382774160447/100000000000000000000)
  directionLo := (119831889236862655957/50000000000000000000)
  directionHi := (47932755694745062383/20000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree024.table
  base := (-1148254793290247293018567826694038826457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-303912658359888778459549923727428660000000000000)
      constant := (1845183973464340721478952842882911658194033538538) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree024.table
  base := (-2305051336815430135176418374825907833647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-101419196937630313677780234131430220000000000000)
      constant := (616439610367565916507890616024989298266411818833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119831889236862655957/50000000000000000000)
  centralHi := (47932755694745062383/20000000000000000000)
  directionLo := (122409213967245995979/50000000000000000000)
  directionHi := (244818427934491991959/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree025.table
  base := (-1477017933177558899667562072621891612451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-949666747611784131992683793390431500000000000000)
      constant := (5982337026591330094509237135003390538634756901002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree025.table
  base := (-1480756732973098750739585751235166681979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-316914887175805296678593325574791750000000000000)
      constant := (1998628805875023127407904905833362836813388320286) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122409213967245995979/50000000000000000000)
  centralHi := (244818427934491991959/100000000000000000000)
  directionLo := (31233345211970875681/12500000000000000000)
  directionHi := (249866761695767005449/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree026.table
  base := (-3545316776963251503411158517339249595901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-987595520143901928606717815598577020000000000000)
      constant := (6452029370407677115910307029734547316837567831451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree026.table
  base := (-710370892501840629855254158816996324483/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33672966000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (2451434943486369411931063985388234000000000000)
      linear := (-65914436707743930464769189751058568000000000000)
      constant := (431117453547180465246123439220818675271779486711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31233345211970875681/12500000000000000000)
  centralHi := (249866761695767005449/100000000000000000000)
  directionLo := (254815098736990831229/100000000000000000000)
  directionHi := (25481509873699083123/10000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree027.table
  base := (-4077098410777481075981770386158002925529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-113947143630668858357861315311858060000000000000)
      constant := (771587578937046759834016591411393676143460241831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree027.table
  base := (-4082807619229561054183326287462936753803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-114076493300544669323032857311931310000000000000)
      constant := (773360283905611646956098028650408964904840201717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254815098736990831229/100000000000000000000)
  centralHi := (25481509873699083123/10000000000000000000)
  directionLo := (64917288956966018611/25000000000000000000)
  directionHi := (51933831165572814889/20000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree028.table
  base := (-4555031653472216653228237695085536368219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-1063453065208137521834785860014868060000000000000)
      constant := (7458828123546784812918232700871123390171797198669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree028.table
  base := (-2280005983943022960265405722299084382857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-354886776264548363614351195116295020000000000000)
      constant := (2492014616355141171250645532549950769744925256138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64917288956966018611/25000000000000000000)
  centralHi := (51933831165572814889/20000000000000000000)
  directionLo := (1322170624696078359/500000000000000000)
  directionHi := (264434124939215671801/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree029.table
  base := (-249192625795001126242685471604028415287/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (7354304830459108235793191956164702000000000000)
      linear := (-220276367548051063689763976444602716000000000000)
      constant := (1599081979289829599327314947058717146254041812548) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree029.table
  base := (-4988192632295969156896245264398121553887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-367544072627462719259603818296796110000000000000)
      constant := (2671309007183997958741450083092982803726047940579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1322170624696078359/500000000000000000)
  centralHi := (264434124939215671801/100000000000000000000)
  directionLo := (269114738311341641067/100000000000000000000)
  directionHi := (67278684577835410267/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree030.table
  base := (-2683766091112633439186557743344130804689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-379770203424124371687617968143719700000000000000)
      constant := (2851277648938830209025555879325124357114154662426) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree030.table
  base := (-1342827717054778988462229290156225834947/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-126733789663459024968285480492432400000000000000)
      constant := (952632443529382342632012045347812431847672038132) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269114738311341641067/100000000000000000000)
  centralHi := (67278684577835410267/25000000000000000000)
  directionLo := (273715323503078762377/100000000000000000000)
  directionHi := (136857661751539381189/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree031.table
  base := (-5709402022506078576302435484822428106857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-1177239382804490911676887926639304620000000000000)
      constant := (9133929008982761517421832524316352653480539808207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree031.table
  base := (-2856344523075886600181542722130681793691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-392858665353291430550109064657798290000000000000)
      constant := (3051723649533207942945065703910842786904223942494) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273715323503078762377/100000000000000000000)
  centralHi := (136857661751539381189/50000000000000000000)
  directionLo := (278239850245086621801/100000000000000000000)
  directionHi := (139119925122543310901/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree032.table
  base := (-375766115823810667929884727899460362541/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-1215168155336608708290921948847450140000000000000)
      constant := (9735556867800146230216145073652863515051421601456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree032.table
  base := (-3007557433571071337672656250548351691129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-405515961716205786195361687838299380000000000000)
      constant := (3252741028937873572457408690498419952148570681386) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278239850245086621801/100000000000000000000)
  centralHi := (139119925122543310901/50000000000000000000)
  directionLo := (282691970541119894997/100000000000000000000)
  directionHi := (141345985270559947499/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree033.table
  base := (-6278446963840336322158536214135194040963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-417698975956242168301651990351865220000000000000)
      constant := (3452865987654930191225382435075165325827625146871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree033.table
  base := (-6280928335390986974277875584148173670647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-139391086026373380613538103672933490000000000000)
      constant := (1153636690453732616135730619344819049004368061833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282691970541119894997/100000000000000000000)
  centralHi := (141345985270559947499/50000000000000000000)
  directionLo := (287075053169784446951/100000000000000000000)
  directionHi := (35884381646223055869/12500000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree034.table
  base := (-162748520305675049937086960450270246113/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (7354304830459108235793191956164702000000000000)
      linear := (-258205140080168860303797998652748236000000000000)
      constant := (2200590543446475519361886152038940975741903826104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree034.table
  base := (-651209439374889081767060501305123589881/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33672966000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (2451434943486369411931063985388234000000000000)
      linear := (-86166110888406899497173386839860312000000000000)
      constant := (735239538815256185921498339401905471732139142954) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287075053169784446951/100000000000000000000)
  centralHi := (35884381646223055869/12500000000000000000)
  directionLo := (4553003336152474261/1562500000000000000)
  directionHi := (58278442702751670541/20000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree035.table
  base := (-1677098946913803658905572448385251490113/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-1328954472932962098133024015471886700000000000000)
      constant := (11668537467291315199696972160829686030031853689052) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree035.table
  base := (-3355131812711034958082096084577862786817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-443487850804948853131119557379802650000000000000)
      constant := (3898576107067031279751773287873287564526845910778) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4553003336152474261/1562500000000000000)
  centralHi := (58278442702751670541/20000000000000000000)
  directionLo := (73911584866844835779/25000000000000000000)
  directionHi := (295646339467379343117/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree036.table
  base := (-1718801007987704811259062518064364981099/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-151875916162786654971895337520003580000000000000)
      constant := (1372809099647227788555776881117322941453241820244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree036.table
  base := (-3438411506629580295698019356221127946849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-152048382389287736258790726853434580000000000000)
      constant := (1376007319473432180612535328471100796721367938622) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73911584866844835779/25000000000000000000)
  centralHi := (295646339467379343117/100000000000000000000)
  directionLo := (149920057017460203269/50000000000000000000)
  directionHi := (299840114034920406539/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree037.table
  base := (-350576798438542082358854443669091119599/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (7354304830459108235793191956164702000000000000)
      linear := (-280962403599439538272218411977635548000000000000)
      constant := (2612625377675913869900838164941900164873045636196) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree037.table
  base := (-7012938409072438501922048273438438482681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-468802443530777564421624803740804830000000000000)
      constant := (4364515619291858817548399513604555421439795549077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149920057017460203269/50000000000000000000)
  centralHi := (299840114034920406539/100000000000000000000)
  directionLo := (303976035121993197663/100000000000000000000)
  directionHi := (9499251097562287427/3125000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree038.table
  base := (-3559187956522415481481244368252481166371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-1442740790529315487975126082096323260000000000000)
      constant := (13792022724750138957287582325358813606807446920842) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree038.table
  base := (-1779897521452437290660265032456745168541/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-481459739893691920066877426921305920000000000000)
      constant := (4608040585332896345985933318228609476938109274788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303976035121993197663/100000000000000000000)
  centralHi := (9499251097562287427/3125000000000000000)
  directionLo := (15402821646738984003/5000000000000000000)
  directionHi := (308056432934779680061/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree039.table
  base := (-1439310380296479516473482348796916335819/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33672966000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (2451434943486369411931063985388234000000000000)
      linear := (-98711304204095552305944006953631252000000000000)
      constant := (969461838817253648436657064895204311659561115423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree039.table
  base := (-7197602514199967819547822502242786633311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-164705678752202091904043350033935670000000000000)
      constant := (1619527658451999473820632000926488247825210704929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15402821646738984003/5000000000000000000)
  centralHi := (308056432934779680061/100000000000000000000)
  directionLo := (78020871332817725183/25000000000000000000)
  directionHi := (312083485331270900733/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree040.table
  base := (-7246760693950454251451904860251394666147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-1518598335593551081203194126512614300000000000000)
      constant := (15312806267948603581156441875829736053931376076997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree040.table
  base := (-1811917328514714944923003178312903518869/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-506774332619520631357382673282308100000000000000)
      constant := (5116131111242928448252155894860257324895687609092) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78020871332817725183/25000000000000000000)
  centralHi := (312083485331270900733/100000000000000000000)
  directionLo := (316059231411656046527/100000000000000000000)
  directionHi := (4938425490807125727/1562500000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree041.table
  base := (-7269588737028365788384514572788461146531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-1556527108125668877817228148720759820000000000000)
      constant := (16104629160725943869371661560350172993930810928581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree041.table
  base := (-7270374171730801314583005861315158516069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-519431628982434987002635296462809190000000000000)
      constant := (5380675165768472003115842016285113558501899054673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316059231411656046527/100000000000000000000)
  centralHi := (4938425490807125727/1562500000000000000)
  directionLo := (159992791794302343249/50000000000000000000)
  directionHi := (319985583588604686499/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree042.table
  base := (-7265529749485147150971153627717907006899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-531485293552595558143754056976301780000000000000)
      constant := (5639123774375947229134660041746890009882764103783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree042.table
  base := (-3633104191711377508396118580072981004441/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-177362975115116447549295973214436760000000000000)
      constant := (1884068955744130865293829823930920287706270785998) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159992791794302343249/50000000000000000000)
  centralHi := (319985583588604686499/100000000000000000000)
  directionLo := (161932169170113544167/50000000000000000000)
  directionHi := (64772867668045417667/20000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree043.table
  base := (-723499948011191566645871085325563047943/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (7354304830459108235793191956164702000000000000)
      linear := (-326476930637980894209059238627410172000000000000)
      constant := (3550202351182387056591960905764757297667276973186) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree043.table
  base := (-7235585574767755330523660331613908257709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-544746221708263698293140542823811370000000000000)
      constant := (5930719251633751277890843946012150213555522802553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161932169170113544167/50000000000000000000)
  centralHi := (64772867668045417667/20000000000000000000)
  directionLo := (327697185817282010857/100000000000000000000)
  directionHi := (163848592908641005429/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree044.table
  base := (-7178348097443581552745631060586848524713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-1670313425722022267659330215345196380000000000000)
      constant := (18605532772258469203668614385729648024370283486863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree044.table
  base := (-7178854055983200009251411110783900523347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-557403518071178053938393166004312460000000000000)
      constant := (6216206454653494105563299961700168862164977131399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327697185817282010857/100000000000000000000)
  centralHi := (163848592908641005429/50000000000000000000)
  directionLo := (41435714806300294887/12500000000000000000)
  directionHi := (331485718450402359097/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree045.table
  base := (-1419174119050991584951081681798940423959/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (168364830)
      previous := (84182415)
      next := (84182415)
      square := (817144981162123137310354661796078000000000000)
      linear := (-37960937738980890317185871945629820000000000000)
      constant := (432909321604320426867058896195958776711333834601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree045.table
  base := (-3548153598147147561904882915390671089617/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-190020271478030803194548596394937850000000000000)
      constant := (2169554512328549391238586476518949539394047935326) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41435714806300294887/12500000000000000000)
  centralHi := (331485718450402359097/100000000000000000000)
  directionLo := (41903929835210673773/12500000000000000000)
  directionHi := (67046287736337078037/20000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree046.table
  base := (-218369235459754490857871534122550490113/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (14322150)
      previous := (7161075)
      next := (7161075)
      square := (69511387811522762153054744387190000000000000)
      linear := (-3300890303943776674645365330361980000000000000)
      constant := (38520149907433351313473527678521272212912660704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree046.table
  base := (-174704803456555753797744750869165505651/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 63654000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (4634092520768184143536982959146000000000000)
      linear := (-220309304649151896116785789174032000000000000)
      constant := (2573945685300069353212461669433982555613164984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41903929835210673773/12500000000000000000)
  centralHi := (67046287736337078037/20000000000000000000)
  directionLo := (338935765927123365897/100000000000000000000)
  directionHi := (169467882963561682949/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree047.table
  base := (-685439239154910196519540159821277526881/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (7354304830459108235793191956164702000000000000)
      linear := (-356819948663675131500286456393926588000000000000)
      constant := (4258848335653607753226192019131579835282316002862) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree047.table
  base := (-6854717120133672389484258598744948243921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-595375407159921120874151035545815730000000000000)
      constant := (7114471350552899938422276886645585700055344230157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338935765927123365897/100000000000000000000)
  centralHi := (169467882963561682949/50000000000000000000)
  directionLo := (68520008572275858729/20000000000000000000)
  directionHi := (171300021430689646823/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree048.table
  base := (-267831109313765503797558904306033113723/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6734593200000000000000000000000000000000000000
      center := (101018898)
      previous := (50509449)
      next := (50509449)
      square := (490286988697273882386212797077646800000000000)
      linear := (-24293713544673246054872884055703712800000000000)
      constant := (296428769141279603369719240446672833883365643791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree048.table
  base := (-52312950238525073241075938766757230611/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-202677567840945158839801219575438940000000000000)
      constant := (2475938540392362260912231210294847132658808272512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68520008572275858729/20000000000000000000)
  centralHi := (171300021430689646823/50000000000000000000)
  directionLo := (13849021644152750637/4000000000000000000)
  directionHi := (173112770551909382963/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree049.table
  base := (-6512120411420828045323401194492406862087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-1859957288382611250729500326385923980000000000000)
      constant := (23190899804541936313481772395305030454712166639937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree049.table
  base := (-3256180791629845187633275291599983359843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-620689999885749832164656281906817910000000000000)
      constant := (7748116659142983162184823649250993657223440895662) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13849021644152750637/4000000000000000000)
  centralHi := (173112770551909382963/50000000000000000000)
  directionLo := (87453366593518451907/25000000000000000000)
  directionHi := (349813466374073807629/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree050.table
  base := (-6303545935375066913611299649266220425457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-1897886060914729047343534348594069500000000000000)
      constant := (24170461695761168323629085725976369951997621356807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree050.table
  base := (-315187683474543474506272242472959675887/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33672966000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (2451434943486369411931063985388234000000000000)
      linear := (-126669459249732837561981781017463800000000000000)
      constant := (1615074473017959117758338223927377295828972058316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87453366593518451907/25000000000000000000)
  centralHi := (349813466374073807629/100000000000000000000)
  directionLo := (176682481588199934373/50000000000000000000)
  directionHi := (353364963176399868747/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree051.table
  base := (-6070160144724877723686756343266476542437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-645271611148948947985856123600738340000000000000)
      constant := (8390279337777557921636819794004367723223360670929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree051.table
  base := (-6070339019097214132108759757557634180117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-215334864203859514485053842755940030000000000000)
      constant := (2803193656333404490931916749766579917702080397163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176682481588199934373/50000000000000000000)
  centralHi := (353364963176399868747/100000000000000000000)
  directionLo := (89220279766104607553/25000000000000000000)
  directionHi := (356881119064418430213/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree052.table
  base := (-2906026152927609547665733070141709318773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-1973743605978964640571602393010360540000000000000)
      constant := (26192024248460534155552919455559054860781220827846) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree052.table
  base := (-1453051570399147111874655275833945237851/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-658661888974492899100414151448321180000000000000)
      constant := (8750740978328136336301812514074023560719962727868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89220279766104607553/25000000000000000000)
  centralHi := (356881119064418430213/100000000000000000000)
  directionLo := (90090742132822939073/25000000000000000000)
  directionHi := (360362968531291756293/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree053.table
  base := (-5529297716590944637646737105203547825913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-2011672378511082437185636415218506060000000000000)
      constant := (27234016597893105241255097491077551606467986448063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree053.table
  base := (-1105886043869322434035739582567935599781/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33672966000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (2451434943486369411931063985388234000000000000)
      linear := (-134263837067481450949133354925764454000000000000)
      constant := (1819770226867680214947976199285017424429192389777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90090742132822939073/25000000000000000000)
  centralHi := (360362968531291756293/100000000000000000000)
  directionLo := (9095287414119259889/2500000000000000000)
  directionHi := (363811496564770395561/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree054.table
  base := (-522195989979975625685351515279807867661/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (168364830)
      previous := (84182415)
      next := (84182415)
      square := (817144981162123137310354661796078000000000000)
      linear := (-45546692245404449639992676387258924000000000000)
      constant := (628818041180563122196389418625659964395239549158) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree054.table
  base := (-5222073890712502449669132666821009078137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-227992160566773870130306465936441120000000000000)
      constant := (3151303458449971233926917119772725628871033575943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9095287414119259889/2500000000000000000)
  centralHi := (363811496564770395561/100000000000000000000)
  directionLo := (367227641901737987937/100000000000000000000)
  directionHi := (183613820950868993969/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree055.table
  base := (-305630778182690491765963270342272935671/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-2087529923575318030413704459634797100000000000000)
      constant := (29380407307081026209846260384818634041786325515536) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree055.table
  base := (-611273811055537301053357181837170694639/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-696633778063235966036172020989824450000000000000)
      constant := (9815917805783842460489842547397659097152898282904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367227641901737987937/100000000000000000000)
  centralHi := (183613820950868993969/50000000000000000000)
  directionLo := (46326537501590995283/12500000000000000000)
  directionHi := (74122460002545592453/20000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree056.table
  base := (-4533740594356233263801053402361360866853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-2125458696107435827027738481842942620000000000000)
      constant := (30484800675500868665522981457168111723725092606003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree056.table
  base := (-3627059910430779408057732026377233049/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6734593200000000000000000000000000000000000000
      center := (101018898)
      previous := (50509449)
      next := (50509449)
      square := (490286988697273882386212797077646800000000000)
      linear := (-28371642977046012867256985766813021600000000000)
      constant := (407394906803786153848383925328546053009173666650) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46326537501590995283/12500000000000000000)
  centralHi := (74122460002545592453/20000000000000000000)
  directionLo := (93491581460825072863/25000000000000000000)
  directionHi := (373966325843300291453/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree057.table
  base := (-4152942494818579727644903419958984340287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-721129156213184541213924168017029380000000000000)
      constant := (10536663343568642145220439531773150779457491709379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree057.table
  base := (-4153014952091947976280072697641582690809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-240649456929688225775559089116942210000000000000)
      constant := (3520258110269792837885839068845792165144366671751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93491581460825072863/25000000000000000000)
  centralHi := (373966325843300291453/100000000000000000000)
  directionLo := (37729053633605841631/10000000000000000000)
  directionHi := (377290536336058416311/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree058.table
  base := (-3747730362488287175680086585742805660393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-2201316241171671420255806526259233660000000000000)
      constant := (32755973745777846450697663752664604270379468446543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree058.table
  base := (-468474078663227795348687711244836736213/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-734605667151979032971929890531327720000000000000)
      constant := (10943622250024253473363524117452169809623794728968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37729053633605841631/10000000000000000000)
  centralHi := (377290536336058416311/100000000000000000000)
  directionLo := (95146428188596425909/25000000000000000000)
  directionHi := (380585712754385703637/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree059.table
  base := (-1659065692250094167114921292116985925987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-2239245013703789216869840548467379180000000000000)
      constant := (33922750447509428420918262296843470554675283697674) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree059.table
  base := (-3318184880630418531353953937969269771383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-747262963514893388617182513711828810000000000000)
      constant := (11333415973811696980085039930556010917471696234011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95146428188596425909/25000000000000000000)
  centralHi := (380585712754385703637/100000000000000000000)
  directionLo := (383852602826627910773/100000000000000000000)
  directionHi := (191926301413313955387/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree060.table
  base := (-1432084255108958998087437148843298836793/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-759057928745302337827958190225174900000000000000)
      constant := (11703439658913653417432493600846894658940829761962) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree060.table
  base := (-286421445986918014577818602009883596881/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (168364830)
      previous := (84182415)
      next := (84182415)
      square := (817144981162123137310354661796078000000000000)
      linear := (-50661350658520516284162342459488660000000000000)
      constant := (782010341271845611282330543093140019326089460318) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383852602826627910773/100000000000000000000)
  centralHi := (191926301413313955387/50000000000000000000)
  directionLo := (387091922727393166487/100000000000000000000)
  directionHi := (48386490340924145811/12500000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree061.table
  base := (-1192930556669240438592632275542485200063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-2315102558768024810097908592883670220000000000000)
      constant := (36318678354917681143696421720481924752908326209426) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree061.table
  base := (-1192950285857813778698581916788561188961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-772577556240722099907687760072830990000000000000)
      constant := (12133839362482719065207873584341149832395196671674) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387091922727393166487/100000000000000000000)
  centralHi := (48386490340924145811/12500000000000000000)
  directionLo := (97576089727710475031/25000000000000000000)
  directionHi := (3122434871286735201/800000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree062.table
  base := (-1883225550230126513125996928995856225599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-2353031331300142606711942615091815740000000000000)
      constant := (37547827755888443169964038991416680618761774815049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree062.table
  base := (-941629713275024707310693017549321919409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-785234852603636455552940383253332080000000000000)
      constant := (12544468431101009514639729906733199509684686002906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97576089727710475031/25000000000000000000)
  centralHi := (3122434871286735201/800000000000000000)
  directionLo := (196745284904630217461/50000000000000000000)
  directionHi := (393490569809260434923/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree063.table
  base := (-135627563083169404397618413845795892633/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (168364830)
      previous := (84182415)
      next := (84182415)
      square := (817144981162123137310354661796078000000000000)
      linear := (-53132446751828008962799480828888028000000000000)
      constant := (862172588491574329832007861355633960554809780174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree063.table
  base := (-135630470825846490081785708854487190401/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (168364830)
      previous := (84182415)
      next := (84182415)
      square := (817144981162123137310354661796078000000000000)
      linear := (-53192809931103387413212867095588878000000000000)
      constant := (864136139636269412107472977343745654130063866878) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196745284904630217461/50000000000000000000)
  centralHi := (393490569809260434923/100000000000000000000)
  directionLo := (3966511874088235077/1000000000000000000)
  directionHi := (396651187408823507701/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree064.table
  base := (-3144621155698876180309452429317612101/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-2428888876364378199940010659508106780000000000000)
      constant := (40068493944638559752166247081653021687496385958656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree064.table
  base := (-402523984380712578089864755841342562657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-810549445329465166843445629614334260000000000000)
      constant := (13386560158318100089502475215528316490493297969338) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3966511874088235077/1000000000000000000)
  centralHi := (396651187408823507701/100000000000000000000)
  directionLo := (399786818713227208717/100000000000000000000)
  directionHi := (199893409356613604359/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree065.table
  base := (-229477551891685386420317691942650024631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-2466817648896495996554044681716252300000000000000)
      constant := (41360009646096262408641256617354251007656051761681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree065.table
  base := (-229498960775666298566336553137929502739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-823206741692379522488698252794835350000000000000)
      constant := (13818022458221736706847046912217770715771936373063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399786818713227208717/100000000000000000000)
  centralHi := (199893409356613604359/50000000000000000000)
  directionLo := (50362255888099119833/12500000000000000000)
  directionHi := (80579609420958591733/20000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree066.table
  base := (185176222954931272846806389387283374379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-834915473809537931056026234641465940000000000000)
      constant := (14224104388833265531298699592996836273897829338114) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree066.table
  base := (370334081488478498895929958209408359371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-278621346018431292711316958658445480000000000000)
      constant := (4752142951873269580250710399115423561427535910731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50362255888099119833/12500000000000000000)
  centralHi := (80579609420958591733/20000000000000000000)
  directionLo := (405985433611686534467/100000000000000000000)
  directionHi := (101496358402921633617/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree067.table
  base := (6215374720307378467993250324989680467/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (7354304830459108235793191956164702000000000000)
      linear := (-508535038792146317956422545226508668000000000000)
      constant := (8801080830231366561077222736735377318114375445856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree067.table
  base := (198888841104380410940425180530234896301/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33672966000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (2451434943486369411931063985388234000000000000)
      linear := (-169704266883641646755840699831167506000000000000)
      constant := (2940355846691302960162228432965280019317578549383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405985433611686534467/100000000000000000000)
  centralHi := (101496358402921633617/25000000000000000000)
  directionLo := (8180990361780957463/2000000000000000000)
  directionHi := (409049518089047873151/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree068.table
  base := (1642839045378367619965287318647170233077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-2580603966492849386396146748340688860000000000000)
      constant := (45359282300508562404625451294231238233881920844573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree068.table
  base := (102676596294985809178682115653676515059/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-861178630781122589424456122336338620000000000000)
      constant := (15154073492891516443069823162909270616532641559952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8180990361780957463/2000000000000000000)
  centralHi := (409049518089047873151/100000000000000000000)
  directionLo := (206045410160536864053/50000000000000000000)
  directionHi := (412090820321073728107/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree069.table
  base := (289435588399272589547428772193950975209/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318270000000000000000000000000000000000000000
      center := (4774050)
      previous := (2387025)
      next := (2387025)
      square := (23170462603840920717684914795730000000000000)
      linear := (-1649989123519197972911267026180740000000000000)
      constant := (29447981954346528419867562416780215021503814744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree069.table
  base := (2315473129792714012588557324910380096181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7723487534613640239228304931910000000000000)
      linear := (-550621252138649618821492593268330000000000000)
      constant := (9838255545344357493917125771030921722440384229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206045410160536864053/50000000000000000000)
  centralHi := (412090820321073728107/100000000000000000000)
  directionLo := (103777460262606109113/25000000000000000000)
  directionHi := (415109841050424436453/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree070.table
  base := (1506196354915397137582718837581547911717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-2656461511557084979624214792756979900000000000000)
      constant := (48129399120576265756081149899716972955175852627866) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree070.table
  base := (753095696624598339168468308005402389997/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-886493223506951300714961368697340800000000000000)
      constant := (16079493335684853645306926587507053634989375442204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103777460262606109113/25000000000000000000)
  centralHi := (415109841050424436453/100000000000000000000)
  directionLo := (83621412588145581817/20000000000000000000)
  directionHi := (209053531470363954543/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree071.table
  base := (3733559479606644829903230029894840769747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-2694390284089202776238248814965125420000000000000)
      constant := (49545637397088851193732028094787564095222656839403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree071.table
  base := (1866775487786992286447365058515702417239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-899150519869865656360213991877841890000000000000)
      constant := (16552618789040198873130890792056362540461806660874) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83621412588145581817/20000000000000000000)
  centralHi := (209053531470363954543/50000000000000000000)
  directionLo := (421082951477419681591/100000000000000000000)
  directionHi := (52635368934677460199/12500000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree072.table
  base := (4478981997832531598160657411915672229037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-303591006291257841428031426352585660000000000000)
      constant := (5664740226512596520167937708094639830972584518957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree072.table
  base := (4478974711396850019630538502205449818251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-303935938744260004001822205019447660000000000000)
      constant := (5677562620086715414416688688360715599457445350411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (421082951477419681591/100000000000000000000)
  centralHi := (52635368934677460199/12500000000000000000)
  directionLo := (84807591162335968499/20000000000000000000)
  directionHi := (6625593059557497539/1562500000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree073.table
  base := (1049731542907121155406401208830458252737/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (7354304830459108235793191956164702000000000000)
      linear := (-554049565830687673893263371876283292000000000000)
      constant := (10488094583270418932284861306415574988763248611913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree073.table
  base := (104973029448913602614350900224612008583/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6734593200000000000000000000000000000000000000
      center := (101018898)
      previous := (50509449)
      next := (50509449)
      square := (490286988697273882386212797077646800000000000)
      linear := (-36978604503827774706028769529553762800000000000)
      constant := (700788020275645803720639959905916702228207067178) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84807591162335968499/20000000000000000000)
  centralHi := (6625593059557497539/1562500000000000000)
  directionLo := (42697250955179926597/10000000000000000000)
  directionHi := (426972509551799265971/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree074.table
  base := (3021292237807592903739968159010367770869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-2808176601685556166080350881589561980000000000000)
      constant := (53919069921502590617399192578410461882787902882362) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree074.table
  base := (1510644782273340028651409555270648576279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-937122408958608723295971861419345160000000000000)
      constant := (18013656693077764707901707595131821010613982347028) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42697250955179926597/10000000000000000000)
  centralHi := (426972509551799265971/100000000000000000000)
  directionLo := (214943515752961529133/50000000000000000000)
  directionHi := (429887031505923058267/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree075.table
  base := (1715190115333778256920101745640408839687/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-948701791405891320898128301265902500000000000000)
      constant := (18472817654050328616683595951103430270169759603284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree075.table
  base := (1372151176529925397444644872339062537693/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (168364830)
      previous := (84182415)
      next := (84182415)
      square := (817144981162123137310354661796078000000000000)
      linear := (-63318647021434871929414965639989750000000000000)
      constant := (1234303759235759136860689413216082203050601684573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214943515752961529133/50000000000000000000)
  centralHi := (429887031505923058267/100000000000000000000)
  directionLo := (432781926379773457407/100000000000000000000)
  directionHi := (422638599980247517/97656250000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree076.table
  base := (7703184134385071495306531218360099203971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-2884034146749791759308418926005853020000000000000)
      constant := (56938621960648583359116245525643353054377913821979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree076.table
  base := (1925795053474387893483323152038398252877/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-962437001684437434586477107780347340000000000000)
      constant := (19022399567688742126680919743051653550127173246364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432781926379773457407/100000000000000000000)
  centralHi := (422638599980247517/97656250000000000)
  directionLo := (217828792716321607451/50000000000000000000)
  directionHi := (435657585432643214903/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree077.table
  base := (4284927098009787346549427294007344670933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-2921962919281909555922452948213998540000000000000)
      constant := (58479576851396464229371861561735897002563824291834) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree077.table
  base := (4284925419821320019124770239074719890053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-975094298047351790231729730960848430000000000000)
      constant := (19537186208930347648041836818086846156817278407198) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217828792716321607451/50000000000000000000)
  centralHi := (435657585432643214903/100000000000000000000)
  directionLo := (438514387094669894177/100000000000000000000)
  directionHi := (219257193547334947089/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree078.table
  base := (9460769549016277647257881984660678883017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-986630563938009117512162323474048020000000000000)
      constant := (20013772526324844128567701342420663060782374709211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree078.table
  base := (473038333801248941423254610965554591277/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (168364830)
      previous := (84182415)
      next := (84182415)
      square := (817144981162123137310354661796078000000000000)
      linear := (-65850106294017743058465490276089968000000000000)
      constant := (1337261086267520973873220665917259433282142878388) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438514387094669894177/100000000000000000000)
  centralHi := (219257193547334947089/50000000000000000000)
  directionLo := (441352697548148173701/100000000000000000000)
  directionHi := (220676348774074086851/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree079.table
  base := (10375929266391727689566360978506044384377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-2997820464346145149150520992630289580000000000000)
      constant := (61623844096561364401720739689698923305024426478273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree079.table
  base := (5187963403770072205690906621007785972347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1000408890773180501522234977321850610000000000000)
      constant := (20587589807522268343608848926417890345282117471202) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441352697548148173701/100000000000000000000)
  centralHi := (220676348774074086851/50000000000000000000)
  directionLo := (55521608909426022859/12500000000000000000)
  directionHi := (444172871275408182873/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree080.table
  base := (11315332564978362630029434013037086927649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-3035749236878262945764555014838435100000000000000)
      constant := (63227156364599598236534894981033706077280653855401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree080.table
  base := (11315330460879286059066301175954139372581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1013066187136094857167487600502351700000000000000)
      constant := (21123206736438907535543065276923979876326090672623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55521608909426022859/12500000000000000000)
  centralHi := (444172871275408182873/100000000000000000000)
  directionLo := (223487625787790260123/50000000000000000000)
  directionHi := (446975251575580520247/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree081.table
  base := (12278978783106335540297514932756511704889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-341519778823375638042065448560731180000000000000)
      constant := (7205694927740961611320032202797126757486221555129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree081.table
  base := (1534872122854710251281153297510004740481/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-341907827833003070937580074560950930000000000000)
      constant := (7221922356588353996815872637784760093214740715528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223487625787790260123/50000000000000000000)
  centralHi := (446975251575580520247/100000000000000000000)
  directionLo := (449760171052380609807/100000000000000000000)
  directionHi := (28110010690773788113/6250000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree082.table
  base := (13266867361751661345566888622638864935097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-3111606781942498538992623059254726140000000000000)
      constant := (66496138023532539733844364788507320233857170231553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree082.table
  base := (2653373164331644200941272193857794148381/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33672966000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (2451434943486369411931063985388234000000000000)
      linear := (-207676155972384713691598569372670776000000000000)
      constant := (4443054159642216496892126609346621421596716184023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449760171052380609807/100000000000000000000)
  centralHi := (28110010690773788113/6250000000000000000)
  directionLo := (452527952074874413227/100000000000000000000)
  directionHi := (113131988018718603307/25000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree083.table
  base := (7139498914305835278776696164110357935439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-3149535554474616335606657081462871660000000000000)
      constant := (68161807362335506335344774854878974149023602926222) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree083.table
  base := (1427899651127508675726486206926048846479/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33672966000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (2451434943486369411931063985388234000000000000)
      linear := (-210207615244967584820649094008770994000000000000)
      constant := (4554343582786011964963134991189058595821826586714) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452527952074874413227/100000000000000000000)
  centralHi := (113131988018718603307/25000000000000000000)
  directionLo := (455278907213032440589/100000000000000000000)
  directionHi := (45527890721303244059/10000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree084.table
  base := (765768489232635405583044738827450362031/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33672966000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (2451434943486369411931063985388234000000000000)
      linear := (-212497621800448942148046073578067812000000000000)
      constant := (4656550823061505617107514001744038335814715107892) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree084.table
  base := (3828842164501574538404808737378087844461/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-354565124195917426582832697741452020000000000000)
      constant := (7778369470097924676358472707384828027421032360884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455278907213032440589/100000000000000000000)
  centralHi := (45527890721303244059/10000000000000000000)
  directionLo := (1145033349124344749/250000000000000000)
  directionHi := (458013339649737899601/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree085.table
  base := (16375982892745864132929042115384877805723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-3225393099538851928834725125879162700000000000000)
      constant := (71555502957265578017893263932430510600899397776627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree085.table
  base := (16375981929314105461912539299028927646731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1076352668950666635393750716404857150000000000000)
      constant := (23905442281703458927021198611382251019332416487073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1145033349124344749/250000000000000000)
  centralHi := (458013339649737899601/100000000000000000000)
  directionLo := (115182885892696570957/25000000000000000000)
  directionHi := (460731543570786283829/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree086.table
  base := (17460836868066319595149412366169354710259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-3263321872070969725448759148087308220000000000000)
      constant := (73283529181978142948647932620392277307100736737291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree086.table
  base := (17460836044311603971344633591119729181371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1089009965313580991039003339585358240000000000000)
      constant := (24482719523429966922567009924416875341326756758193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115182885892696570957/25000000000000000000)
  centralHi := (460731543570786283829/100000000000000000000)
  directionLo := (115858451133574117817/25000000000000000000)
  directionHi := (463433804534296471269/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree087.table
  base := (18569931469982362091198309560666119849979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1100416881534362507354264390098484580000000000000)
      constant := (25010780335968701281088811510615579075530133983857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree087.table
  base := (9284965382872010742629166923584097447931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-367222420558831782228085320921953110000000000000)
      constant := (8355646710492920692318320242124835651334955777782) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115858451133574117817/25000000000000000000)
  centralHi := (463433804534296471269/100000000000000000000)
  directionLo := (233060199910423185321/50000000000000000000)
  directionHi := (466120399820846370643/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree088.table
  base := (19703266495202732781674929568534629087399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-3339179417135205318676827192503599260000000000000)
      constant := (76801938424781331231254255560013465292623896333151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree088.table
  base := (9851632946607707504560123318300042935893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1114324558039409702329508585946360420000000000000)
      constant := (25658104102475881502688620445828971003578865168638) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233060199910423185321/50000000000000000000)
  centralHi := (466120399820846370643/100000000000000000000)
  directionLo := (468791598765548320893/100000000000000000000)
  directionHi := (234395799382774160447/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree089.table
  base := (162975326343647921427385735197963987121/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-3377108189667323115290861214711744780000000000000)
      constant := (78592321423929307201592770957063579524649575210112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree089.table
  base := (10430420628733598572163124243004177497601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1126981854402324057974761209126861510000000000000)
      constant := (26256211433571605870427376534190348789234683554566) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468791598765548320893/100000000000000000000)
  centralHi := (234395799382774160447/50000000000000000000)
  directionLo := (471447663073189932941/100000000000000000000)
  directionHi := (235723831536594966471/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree090.table
  base := (22042657155253493727467487015797401392369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-379448551355493434656099470768876700000000000000)
      constant := (8933721110891338505687775690511308559995598999409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree090.table
  base := (22042656715545034737920388148435187029809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-379879716921746137873337944102454200000000000000)
      constant := (8953754040786362326755049906180135417676399907249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471447663073189932941/100000000000000000000)
  centralHi := (235723831536594966471/50000000000000000000)
  directionLo := (474088847117484069791/100000000000000000000)
  directionHi := (14815276472421377181/3125000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree091.table
  base := (4649742504489364969681997493995597851851/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (7354304830459108235793191956164702000000000000)
      linear := (-690593146946311741703785851825607164000000000000)
      constant := (16447088828173866818856053315732799367922577640099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree091.table
  base := (11624356073358045153309389946871221804381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1152296447128152769265266455487863690000000000000)
      constant := (27473256166805608466372868072609730040697380064046) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474088847117484069791/100000000000000000000)
  centralHi := (14815276472421377181/3125000000000000000)
  directionLo := (476715398225396482833/100000000000000000000)
  directionHi := (238357699112698241417/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree092.table
  base := (24479007770044964167100749477867026590933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (14322150)
      previous := (7161075)
      next := (7161075)
      square := (69511387811522762153054744387190000000000000)
      linear := (-6599044437171411162822236826722460000000000000)
      constant := (158956869276450534051688297999236381565928873773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree092.table
  base := (24479007449020043579431446198976916031117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318270000000000000000000000000000000000000000
      center := (4774050)
      previous := (2387025)
      next := (2387025)
      square := (23170462603840920717684914795730000000000000)
      linear := (-2202180989586138232345026613739820000000000000)
      constant := (53104335661993416124448872299929558306522360759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476715398225396482833/100000000000000000000)
  centralHi := (238357699112698241417/50000000000000000000)
  directionLo := (119831889236862655957/25000000000000000000)
  directionHi := (479327556947450623829/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree093.table
  base := (25733542810608762642735615378816936598891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1176274426598598100582332434514775620000000000000)
      constant := (28653903037574846189766204627683161993159306140353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree093.table
  base := (12866771268177727191419149425177347095267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-392537013284660493518590567282955290000000000000)
      constant := (9572691438692055845629972608443183998403041483974) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119831889236862655957/25000000000000000000)
  centralHi := (479327556947450623829/100000000000000000000)
  directionLo := (96385111462969152807/20000000000000000000)
  directionHi := (120481389328711441009/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree094.table
  base := (27012317570288534532329809463951705743519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-3566752052327912098361031325752472380000000000000)
      constant := (87856019933585845326445462666580405379715280011031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree094.table
  base := (27012317336018330510063006961446185061011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1190268336216895836201024325029366960000000000000)
      constant := (29350898418226480158720739028838430220194565664313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96385111462969152807/20000000000000000000)
  centralHi := (120481389328711441009/25000000000000000000)
  directionLo := (48450962708416626281/10000000000000000000)
  directionHi := (484509627084166262811/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree095.table
  base := (353941649833965174814716700148320423053/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (7354304830459108235793191956164702000000000000)
      linear := (-720936164972005978995013069592123580000000000000)
      constant := (17954223261335225330583555977460848925501662844752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree095.table
  base := (884854118331958910041329670763047749401/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1202925632579810191846276948209868050000000000000)
      constant := (29990665870611930871459686499292144377251302293856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48450962708416626281/10000000000000000000)
  centralHi := (484509627084166262811/100000000000000000000)
  directionLo := (97415997594081235567/20000000000000000000)
  directionHi := (121769996992601544459/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree096.table
  base := (14821293003615039968378267516386065067921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1214203199130715897196366456722921140000000000000)
      constant := (30568999409778438835335961016857179131905891523686) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree096.table
  base := (237140686690750230531529861981287843141/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2244864400000000000000000000000000000000000000
      center := (33672966)
      previous := (16836483)
      next := (16836483)
      square := (163428996232424627462070932359215600000000000)
      linear := (-16207772385902993966553727618538255200000000000)
      constant := (408498355631466311082883626322475361415250188505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97415997594081235567/20000000000000000000)
  centralHi := (121769996992601544459/25000000000000000000)
  directionLo := (489636855868983983917/100000000000000000000)
  directionHi := (244818427934491991959/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree097.table
  base := (6198815917472082376945528723548848498589/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (7354304830459108235793191956164702000000000000)
      linear := (-736107673984853097640626678475381788000000000000)
      constant := (18732733139863485066861117504212349230248207667461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree097.table
  base := (30994079441433955031063439103552029347291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1228240225305638903136782194570870230000000000000)
      constant := (31291030822734050861954883690030034324221166017553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489636855868983983917/100000000000000000000)
  centralHi := (244818427934491991959/50000000000000000000)
  directionLo := (492180441067376593817/100000000000000000000)
  directionHi := (246090220533688296909/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree098.table
  base := (32369812689568295940762750885275962454841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-3718467142456383284817167414585054460000000000000)
      constant := (95641118714726332771804002988828898116538706292609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree098.table
  base := (3236981256496875816251051367900868816883/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33672966000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (2451434943486369411931063985388234000000000000)
      linear := (-248179504333710651756406963550274264000000000000)
      constant := (6390325664222497098927353543985701733041361484978) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492180441067376593817/100000000000000000000)
  centralHi := (246090220533688296909/50000000000000000000)
  directionLo := (98942189689391963249/20000000000000000000)
  directionHi := (247355474223479908123/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree099.table
  base := (33769785282166437221140197828393079272751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-417377323887611231270133492977022220000000000000)
      constant := (10848817474884614557069536598673870972164441524911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree099.table
  base := (4221223146973449364541603567610949522979/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-417851606010489204809095813643957470000000000000)
      constant := (10873056388990214143330002969609460600186650780952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98942189689391963249/20000000000000000000)
  centralHi := (247355474223479908123/50000000000000000000)
  directionLo := (124307144418900884661/25000000000000000000)
  directionHi := (99445715535120707729/20000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree100.table
  base := (3519399733841244087937687267526668179007/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (7354304830459108235793191956164702000000000000)
      linear := (-758864937504123775609047091800269100000000000000)
      constant := (19931676275134455286226953031073815205054953874286) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree100.table
  base := (703879944951974981426384410029198534069/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6734593200000000000000000000000000000000000000
      center := (101018898)
      previous := (50509449)
      next := (50509449)
      square := (490286988697273882386212797077646800000000000)
      linear := (-50648484575775278802901602564494940000000000000)
      constant := (1331746134394634465392614450732369261244955278654) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124307144418900884661/25000000000000000000)
  centralHi := (99445715535120707729/20000000000000000000)
  directionLo := (499733523391534010897/100000000000000000000)
  directionHi := (249866761695767005449/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree101.table
  base := (7328489767148352012833504101203183492233/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (7354304830459108235793191956164702000000000000)
      linear := (-766450692010547334931853896241898204000000000000)
      constant := (20339638203743769239187339386786777787238584609617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree101.table
  base := (36642448758223247125614986594583923029623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1278869410757296325717792687292874590000000000000)
      constant := (33975080899424727198791397623411562594661556135909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499733523391534010897/100000000000000000000)
  centralHi := (249866761695767005449/50000000000000000000)
  directionLo := (502225975378942381459/100000000000000000000)
  directionHi := (25111298768947119073/5000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree102.table
  base := (38115139755119510040251061277543753487371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1290060744194951490424434501139212180000000000000)
      constant := (34586262067379932922758358899879183367346312556193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree102.table
  base := (38115139688956031277176969311035035782821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-430508902373403560454348436824458560000000000000)
      constant := (11554483928444103911406666995821664507453952486181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (502225975378942381459/100000000000000000000)
  centralHi := (25111298768947119073/5000000000000000000)
  directionLo := (504706118735787874183/100000000000000000000)
  directionHi := (63088264841973484273/12500000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree103.table
  base := (19806035040246363914314152819264370547341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (714150)
      previous := (357075)
      next := (357075)
      square := (3466068823856682173528698254390000000000000)
      linear := (-368376944586386301054513858575340000000000000)
      constant := (9976450836565586561717716733612795336351781002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree103.table
  base := (990301750600656004356202760178340372983/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3174000000000000000000000000000000000000000
      center := (47610)
      previous := (23805)
      next := (23805)
      square := (231071254923778811568579883626000000000000)
      linear := (-24586370128817514129669109881306000000000000)
      constant := (666580563998927126063850629262320709375392168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504706118735787874183/100000000000000000000)
  centralHi := (63088264841973484273/12500000000000000000)
  directionLo := (12679353350855387189/2500000000000000000)
  directionHi := (507174134034215487561/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree104.table
  base := (20566619899163756216144674226118427312557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-3946039777649090064501371547833927580000000000000)
      constant := (107942333186988783508721716359716970504607609702186) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree104.table
  base := (10283309937535305618220617100573236021081/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1316841299846039392653550556834377860000000000000)
      constant := (36061023595173258703924991552019095034095671592492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12679353350855387189/2500000000000000000)
  centralHi := (507174134034215487561/100000000000000000000)
  directionLo := (254815098736990831229/50000000000000000000)
  directionHi := (509630197473981662459/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree105.table
  base := (66685388901902958508321856896580539619/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 33672966000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (2451434943486369411931063985388234000000000000)
      linear := (-265597903345413857407693704669471540000000000000)
      constant := (7337685665810474434275848380373642609718543357056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree105.table
  base := (42678648856101294198418512064846761179891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-443166198736317916099601060004959650000000000000)
      constant := (12256741506231418783659781484842318151570098254451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254815098736990831229/50000000000000000000)
  centralHi := (509630197473981662459/100000000000000000000)
  directionLo := (512074481029256830857/100000000000000000000)
  directionHi := (256037240514628415429/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree106.table
  base := (2212414868377765718422765667556396945287/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (7354304830459108235793191956164702000000000000)
      linear := (-804379464542665131545887918450043724000000000000)
      constant := (22441804465028796791009427215126346216526918067452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree106.table
  base := (22124148666237133199957552481211162189217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1342155892571868103944055803195380040000000000000)
      constant := (37486368787727277454294707059199055973217989607622) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (512074481029256830857/100000000000000000000)
  centralHi := (256037240514628415429/50000000000000000000)
  directionLo := (514507152589150972883/100000000000000000000)
  directionHi := (128626788147287743221/25000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree107.table
  base := (45842185201249339355590929234105966609897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-4059826095245443454343473614458364140000000000000)
      constant := (114373545200540742374694274900942012621078295416753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree107.table
  base := (22921092585660236088740768525901789689513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1354813188934782459589308426375881130000000000000)
      constant := (38209456402138645947085406724534863226054121805558) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514507152589150972883/100000000000000000000)
  centralHi := (128626788147287743221/25000000000000000000)
  directionLo := (516928376092287132787/100000000000000000000)
  directionHi := (129232094023071783197/25000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree108.table
  base := (237301561957458237261965405463360116423/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2244864400000000000000000000000000000000000000
      center := (33672966)
      previous := (16836483)
      next := (16836483)
      square := (163428996232424627462070932359215600000000000)
      linear := (-18212243856789161115366700607406709600000000000)
      constant := (518039349391126698813601275552009130994756960824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree108.table
  base := (4746031236596046046429440609906605304941/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (168364830)
      previous := (84182415)
      next := (84182415)
      square := (817144981162123137310354661796078000000000000)
      linear := (-91164699019846454348970736637092148000000000000)
      constant := (2595965824121060224334369291654716319869565975002) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516928376092287132787/100000000000000000000)
  centralHi := (129232094023071783197/25000000000000000000)
  directionLo := (64917288956966018611/12500000000000000000)
  directionHi := (519338311655728148889/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree109.table
  base := (9820535786511321619263370259540326080913/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (7354304830459108235793191956164702000000000000)
      linear := (-827136728061935809514308331774931036000000000000)
      constant := (23752989512448616017050693708642878575627245046937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree109.table
  base := (6137834863847342376298624883536927998423/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1380127781660611170879813672736883310000000000000)
      constant := (39676461666664504568281942368427650827441382930472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64917288956966018611/12500000000000000000)
  centralHi := (519338311655728148889/100000000000000000000)
  directionLo := (521737115698543521563/100000000000000000000)
  directionHi := (130434278924635880391/25000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree110.table
  base := (12692321204908192682714693897464537485371/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-4173612412841796844185575681082800700000000000000)
      constant := (120991827048016437214774086186648741141703739082316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree110.table
  base := (25384642400528987756992549660522058140189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1392785078023525526525066295917384400000000000000)
      constant := (40420379316605026271780342218186041556004607430574) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521737115698543521563/100000000000000000000)
  centralHi := (130434278924635880391/25000000000000000000)
  directionLo := (52412494106028627101/10000000000000000000)
  directionHi := (524124941060286271011/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree111.table
  base := (26230065024340239706048647802222004848081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1403847061791304880266536567763648740000000000000)
      constant := (41079830690039845941915029039094294613701266678246) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree111.table
  base := (6557516254104866632383453242575808853627/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-468480791462146627390106306365961830000000000000)
      constant := (13723746770523602950160426195499392579434241263576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52412494106028627101/10000000000000000000)
  centralHi := (524124941060286271011/100000000000000000000)
  directionLo := (526501937114633725619/100000000000000000000)
  directionHi := (26325096855731686281/5000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree112.table
  base := (13543803654077891307740724998991674100823/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-4249469957906032437413643725499091740000000000000)
      constant := (125507942628381247373450439214356745497680560706108) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree112.table
  base := (27087607301401074337841129236011274825999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1418099670749354237815571542278386580000000000000)
      constant := (41929044651505964222521986046247574112832520243034) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526501937114633725619/100000000000000000000)
  centralHi := (26325096855731686281/5000000000000000000)
  directionLo := (1322170624696078359/250000000000000000)
  directionHi := (528868249878431343601/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree113.table
  base := (27957269259843848170537298648837485667177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-4287398730438150234027677747707237260000000000000)
      constant := (127797178722658203280250285954811019223189015310946) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree113.table
  base := (55914538508167982829912893844919665759677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1430756967112268593460824165458887670000000000000)
      constant := (42693792336363693034143558204663653131428483895991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1322170624696078359/250000000000000000)
  centralHi := (528868249878431343601/100000000000000000000)
  directionLo := (531224022116364823931/100000000000000000000)
  directionHi := (132806005529091205983/25000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree114.table
  base := (28839050878217247598105251859073456400503/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1441775834323422676880570589971794260000000000000)
      constant := (43369066784276825681522329318866317608876619901898) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree114.table
  base := (11535620349322438123378899208357361581761/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (168364830)
      previous := (84182415)
      next := (84182415)
      square := (817144981162123137310354661796078000000000000)
      linear := (-96227617565012196607071785909292584000000000000)
      constant := (2897698891073657545034493217702880196732057395521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531224022116364823931/100000000000000000000)
  centralHi := (132806005529091205983/25000000000000000000)
  directionLo := (533569393441472833037/100000000000000000000)
  directionHi := (266784696720736416519/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree115.table
  base := (1486647608114224508113588870600688718701/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190962000000000000000000000000000000000000000
      center := (2864430)
      previous := (1432215)
      next := (1432215)
      square := (13902277562304552430610948877438000000000000)
      linear := (-1649624300757045681382134514980540000000000000)
      constant := (50071080347371610345890870008281394876402321448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree115.table
  base := (59465904316194607275275197315939250668107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318270000000000000000000000000000000000000000
      center := (4774050)
      previous := (2387025)
      next := (2387025)
      square := (23170462603840920717684914795730000000000000)
      linear := (-2752498222756327608225575447674650000000000000)
      constant := (83637273611903230804578084027506461031013841489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533569393441472833037/100000000000000000000)
  centralHi := (266784696720736416519/50000000000000000000)
  directionLo := (535904500411700592949/100000000000000000000)
  directionHi := (10718090008234011859/2000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree116.table
  base := (2451117848897530732935438271273993591303/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20203779600000000000000000000000000000000000000
      center := (303056694)
      previous := (151528347)
      next := (151528347)
      square := (1470860966091821647158638391232940400000000000)
      linear := (-176047401921380144954791192573266952800000000000)
      constant := (5391584008819080560450494800606920446726245722047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree116.table
  base := (61277946215298913953751385612212800781527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1468728856201011660396582035000390940000000000000)
      constant := (45029695460112317669594229967481430932740566049541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535904500411700592949/100000000000000000000)
  centralHi := (10718090008234011859/2000000000000000000)
  directionLo := (107645895324536656427/20000000000000000000)
  directionHi := (67278684577835410267/12500000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree117.table
  base := (31557113724333895749746531544208424541687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-493234868951846824498201537393313260000000000000)
      constant := (15240219828644262480767895152147651552168597311214) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree117.table
  base := (12622845488516353014703324600052180742913/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (168364830)
      previous := (84182415)
      next := (84182415)
      square := (817144981162123137310354661796078000000000000)
      linear := (-98759076837595067736122310545392802000000000000)
      constant := (3054814434955251445495597937588660476230327364993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107645895324536656427/20000000000000000000)
  centralHi := (67278684577835410267/12500000000000000000)
  directionLo := (540544452796937634439/100000000000000000000)
  directionHi := (13513611319923440861/2500000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree118.table
  base := (64974748002117556789888968161377533360267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-4477042593098739217097847858747964860000000000000)
      constant := (139555142230704373890352674943131272531006204662883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree118.table
  base := (64974747996929825127660133171173949176501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1494043448926840371687087281361393120000000000000)
      constant := (46621680933327426479805624071754587115353023085983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540544452796937634439/100000000000000000000)
  centralHi := (13513611319923440861/2500000000000000000)
  directionLo := (542849556869630231727/100000000000000000000)
  directionHi := (33928097304351889483/6250000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree119.table
  base := (13371901576369039990421085345962468156083/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (7354304830459108235793191956164702000000000000)
      linear := (-902994273126171402742376376191222076000000000000)
      constant := (28393818307829490080588570453589846913243798328267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree119.table
  base := (66859507877423487928291956310537515380613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1506700745289754727332339904541894210000000000000)
      constant := (47428088687092799127760090876969399281067929304079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542849556869630231727/100000000000000000000)
  centralHi := (33928097304351889483/6250000000000000000)
  directionLo := (109028982814216344649/20000000000000000000)
  directionHi := (272572457035540861623/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree120.table
  base := (68768507087074781996133607348441277308369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1517633379387658270108638634388085300000000000000)
      constant := (48134608794362799871279541920782594641900640426227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree120.table
  base := (68768507083306241565224369533993164358201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-506452680550889694325864175907465100000000000000)
      constant := (16080479928537384208794065452107710611277685682361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109028982814216344649/20000000000000000000)
  centralHi := (272572457035540861623/50000000000000000000)
  directionLo := (273715323503078762377/50000000000000000000)
  directionHi := (109486129401231504951/20000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree121.table
  base := (70701745617170437923386798379354348310241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-4590828910695092606939949925372401420000000000000)
      constant := (146859346762495104332322994842774199268904353967209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree121.table
  base := (7070174561395880309228557590148235743907/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33672966000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (2451434943486369411931063985388234000000000000)
      linear := (-306403067603116687724569030180579278000000000000)
      constant := (9812346845775012085775305827111007433664565118162) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273715323503078762377/50000000000000000000)
  centralHi := (109486129401231504951/20000000000000000000)
  directionLo := (549706875730687411987/100000000000000000000)
  directionHi := (137426718932671852997/25000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree122.table
  base := (4541201466975882854454061918569845071697/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-4628757683227210403553983947580546940000000000000)
      constant := (149335652677341398539255209540907835721388495439248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree122.table
  base := (72659223468877282784271201802073089226477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1544672634378497794268097774083397480000000000000)
      constant := (49888972016873038804450811106839009961519063160391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549706875730687411987/100000000000000000000)
  centralHi := (137426718932671852997/25000000000000000000)
  directionLo := (137993429456262196957/25000000000000000000)
  directionHi := (551973717825048787829/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree123.table
  base := (74640940649986839648526329371118275136587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1555562151919776066722672656596230820000000000000)
      constant := (50610914709202039497697908179488507210326469703521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree123.table
  base := (74640940647654752574726848515469121971439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-519109976913804049971116799087966190000000000000)
      constant := (16907717716533078838543986638615186950532353069679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137993429456262196957/25000000000000000000)
  centralHi := (551973717825048787829/100000000000000000000)
  directionLo := (138557822116260309003/25000000000000000000)
  directionHi := (554231288465041236013/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree124.table
  base := (76646897151952751693243056618090006128631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-4704615228291445996782051991996837980000000000000)
      constant := (154350621113272301698420886012008999401963774934319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree124.table
  base := (76646897149965690258067479453737874564487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1569987227104326505558603020444399660000000000000)
      constant := (51564277627048172913339520589007584931561117779221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138557822116260309003/25000000000000000000)
  centralHi := (554231288465041236013/100000000000000000000)
  directionLo := (556479700490173243603/100000000000000000000)
  directionHi := (139119925122543310901/25000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree125.table
  base := (15735418595449165097183166885582108986447/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (7354304830459108235793191956164702000000000000)
      linear := (-948508800164712758679217202840996700000000000000)
      constant := (31377856726865302161464958888556448369163386437703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree125.table
  base := (78677092975552852978220537674642500575079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1582644523467240861203855643624900750000000000000)
      constant := (52412345449215516932600356074600579554509807807157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556479700490173243603/100000000000000000000)
  centralHi := (139119925122543310901/25000000000000000000)
  directionLo := (558719064469475650307/100000000000000000000)
  directionHi := (139679766117368912577/25000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree126.table
  base := (40365764062829260383331821791382918603397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-531163641483964621112235559601458780000000000000)
      constant := (17716525743417584786181504749392783343704318221834) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree126.table
  base := (80731528124216202761277275708184292471051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-531767273276718405616369422268467280000000000000)
      constant := (17755785538699300212489132434098206157018626051211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558719064469475650307/100000000000000000000)
  centralHi := (139679766117368912577/25000000000000000000)
  directionLo := (280474744382475218589/50000000000000000000)
  directionHi := (560949488764950437179/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree127.table
  base := (82810202597032263132787770312215651047411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-4818401545887799386624154058621274540000000000000)
      constant := (162028965282559548997641314771713775543581002486539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree127.table
  base := (82810202595803565351219702993700571209019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1607959116193069572494360889985902930000000000000)
      constant := (54129311127692761948666159726320944016750937840177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280474744382475218589/50000000000000000000)
  centralHi := (560949488764950437179/100000000000000000000)
  directionLo := (4505368636742063/800000000000000)
  directionHi := (563171079592757875001/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree128.table
  base := (21228279097812351354446653257777286370249/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-4856330318419917183238188080829420060000000000000)
      constant := (164629984409724426279791703370634922637105947931204) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree128.table
  base := (84913116390202753039852539233164276589967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1620616412555983928139613513166404020000000000000)
      constant := (54998208983998212019754804549261588659014277366061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4505368636742063/800000000000000)
  centralHi := (563171079592757875001/100000000000000000000)
  directionLo := (282691970541119894997/50000000000000000000)
  directionHi := (113076788216447957999/20000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree129.table
  base := (10880033688528306137525950735329855119333/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1631419696984011659950740701012521860000000000000)
      constant := (55750596357416225819257941586744977560872904206712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree129.table
  base := (87040269507334923950723117962479711302731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-544424569639632761261622045448968370000000000000)
      constant := (18624683395004307810273582783963045026564446111691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282691970541119894997/50000000000000000000)
  centralHi := (113076788216447957999/20000000000000000000)
  directionLo := (567588175332871749617/100000000000000000000)
  directionHi := (283794087666435874809/50000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree130.table
  base := (44595830973954165032476309031613266483699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-4932187863484152776466256125245711100000000000000)
      constant := (169894379270129521273474399772695143342363607943702) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree130.table
  base := (44595830973574492765062789242974635776911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1645931005281812639430118759527406200000000000000)
      constant := (56756834730736035962952095823600102399378307688026) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (567588175332871749617/100000000000000000000)
  centralHi := (283794087666435874809/50000000000000000000)
  directionLo := (142445970617308075973/25000000000000000000)
  directionHi := (569783882469232303893/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree131.table
  base := (91367293710263603358651098037318424634659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-4970116636016270573080290147453856620000000000000)
      constant := (172557755003365369459624851157128628425844652392891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree131.table
  base := (91367293709616879820105819052484387375529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1658588301644726995075371382707907290000000000000)
      constant := (57646562621167077218816738015482017678313508624507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (142445970617308075973/25000000000000000000)
  centralHi := (569783882469232303893/100000000000000000000)
  directionLo := (285985580347036509579/50000000000000000000)
  directionHi := (571971160694073019159/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree132.table
  base := (23391791198820096801171983084669509155277/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1669348469516129456564774723220667380000000000000)
      constant := (58413972090651873958078402815761101086044662283164) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree132.table
  base := (93567164794729613286910047585087942911903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-557081866002547116906874668629469460000000000000)
      constant := (19514411285435298592978839760348328094780408452383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (285985580347036509579/50000000000000000000)
  centralHi := (571971160694073019159/100000000000000000000)
  directionLo := (287075053169784446951/50000000000000000000)
  directionHi := (574150106339568893903/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree133.table
  base := (19158255040592589639881733561407277885513/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (7354304830459108235793191956164702000000000000)
      linear := (-1009194836216101233261671638374029532000000000000)
      constant := (35589372615180098804147198125527534598587146712337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree133.table
  base := (4789563760124695763512221677565577054597/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33672966000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (2451434943486369411931063985388234000000000000)
      linear := (-336780578874111141273175325813781894000000000000)
      constant := (11889369687230520988345000753504910766359649849404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287075053169784446951/50000000000000000000)
  centralHi := (574150106339568893903/100000000000000000000)
  directionLo := (576320813916824834361/100000000000000000000)
  directionHi := (288160406958412417181/50000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree134.table
  base := (98039624933328827913329587870975160915071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-5083902953612623962922392214078293180000000000000)
      constant := (180672595415200871914188569819697229030506572005879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree134.table
  base := (3063738279154044597175486275273666293279/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1696560190733470062011129252249410560000000000000)
      constant := (60357406360707535398260891302427319162622876728224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (576320813916824834361/100000000000000000000)
  centralHi := (288160406958412417181/50000000000000000000)
  directionLo := (57848337616371017579/10000000000000000000)
  directionHi := (578483376163710175791/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree135.table
  base := (50156106993203213294558540878714277599799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-569092414016082417726269581809604300000000000000)
      constant := (20379901476650910003911276848237105997777531111278) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree135.table
  base := (100312213986066339205598047708353392747193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-569739162365461472552127291809970550000000000000)
      constant := (20424969209990398482903406545950056472493479414073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57848337616371017579/10000000000000000000)
  centralHi := (578483376163710175791/100000000000000000000)
  directionLo := (580637884091089749731/100000000000000000000)
  directionHi := (145159471022772437433/25000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree136.table
  base := (102609042362232972700526003220931519912077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-5159760498676859556150460258494584220000000000000)
      constant := (186186416699874328773471224695164989297491537715573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree136.table
  base := (51304521180971703059249531497306190773107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1721874783459298773301634498610412740000000000000)
      constant := (62199352243944237583568772895138222773492345725362) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (580637884091089749731/100000000000000000000)
  centralHi := (145159471022772437433/25000000000000000000)
  directionLo := (4553003336152474261/781250000000000000)
  directionHi := (582784427027516705409/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree137.table
  base := (26232527515213204546075769647254459437981/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-5197689271208977352764494280702729740000000000000)
      constant := (188974505645251528320884929002147859876021079929876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree137.table
  base := (52465055030303140329953314709194224430719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1734532079822213128946887121790913830000000000000)
      constant := (63130740202627430435622755022339848549151970242554) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4553003336152474261/781250000000000000)
  centralHi := (582784427027516705409/100000000000000000000)
  directionLo := (29246154633122459117/5000000000000000000)
  directionHi := (584923092662449182341/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree138.table
  base := (26818854270579002123435559954378450629829/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318270000000000000000000000000000000000000000
      center := (4774050)
      previous := (2387025)
      next := (2387025)
      square := (23170462603840920717684914795730000000000000)
      linear := (-3299066190133015216999702774360980000000000000)
      constant := (120846490312534540923574944104105131792782270332) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree138.table
  base := (53637708541053058551366726998995834990249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1591350)
      previous := (795675)
      next := (795675)
      square := (7723487534613640239228304931910000000000000)
      linear := (-1100938485308838994702041427203160000000000000)
      constant := (40371185574052700228682065640612983626823103282) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29246154633122459117/5000000000000000000)
  centralHi := (584923092662449182341/100000000000000000000)
  directionLo := (146763491772012497573/25000000000000000000)
  directionHi := (587053967088049990293/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree139.table
  base := (5482248171333854225653075757124407063391/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (7354304830459108235793191956164702000000000000)
      linear := (-1054709363254642589198512465023804156000000000000)
      constant := (38922608028419889595593314394087243092894349926236) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree139.table
  base := (109644963426498401383461392559494926580503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1759846672548041840237392368151916010000000000000)
      constant := (65014346154127786253482138188501219202458886890949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146763491772012497573/25000000000000000000)
  centralHi := (587053967088049990293/100000000000000000000)
  directionLo := (294588567419812835607/50000000000000000000)
  directionHi := (117835426967925134243/20000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree140.table
  base := (56019374546997040019986756336710770726419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-5311475588805330742606596347327166300000000000000)
      constant := (197463485693575854172790177329774775003513506866262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree140.table
  base := (112038749093841972716780042235806697603031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1772503968910956195882644991332417100000000000000)
      constant := (65966564146946874052751709825290153455479572179973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294588567419812835607/50000000000000000000)
  centralHi := (117835426967925134243/20000000000000000000)
  directionLo := (591292678934758686233/100000000000000000000)
  directionHi := (295646339467379343117/50000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree141.table
  base := (57228387042163842089496621885550424021853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1783134787112482846406876789845103940000000000000)
      constant := (66778238926808200134471203002430868839373439325998) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree141.table
  base := (114456774084198206573956669821015209694127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-595053755091290183842632538170972730000000000000)
      constant := (22308575161493310669268587135951579567752201478447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (591292678934758686233/100000000000000000000)
  centralHi := (295646339467379343117/50000000000000000000)
  directionLo := (593400680911183979837/100000000000000000000)
  directionHi := (296700340455591989919/50000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree142.table
  base := (23379807679548108550023559350805956948457/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (7354304830459108235793191956164702000000000000)
      linear := (-1077466626773913267166932878348691468000000000000)
      constant := (40645346680529770175137414623112333919384284470193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree142.table
  base := (58449519198815166824732121716974387524491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1797818561636784907173150237693419280000000000000)
      constant := (67891830166728024701156865257887169803983009610306) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (593400680911183979837/100000000000000000000)
  centralHi := (296700340455591989919/50000000000000000000)
  directionLo := (595501220863458814803/100000000000000000000)
  directionHi := (148875305215864703701/25000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree143.table
  base := (3730173188571771151303393470468737243983/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-5425261906401684132448698413951602860000000000000)
      constant := (206139535560251839259508085262990142317419516651744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree143.table
  base := (4774621681368114935545019873855027885631/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6734593200000000000000000000000000000000000000
      center := (101018898)
      previous := (50509449)
      next := (50509449)
      square := (490286988697273882386212797077646800000000000)
      linear := (-72419034319987970512736114434956814800000000000)
      constant := (2754595127747689536533974680481973987160952275773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (595501220863458814803/100000000000000000000)
  centralHi := (148875305215864703701/25000000000000000000)
  directionLo := (298797188739236268571/50000000000000000000)
  directionHi := (597594377478472537143/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree144.table
  base := (121856284994061000036965888537407868941677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-607021186548200214340303604017749820000000000000)
      constant := (23230347028137427144910745148105994523167590933997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree144.table
  base := (761601781212382274904288300845410899979/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (168364830)
      previous := (84182415)
      next := (84182415)
      square := (817144981162123137310354661796078000000000000)
      linear := (-121542210290840907897577032270294764000000000000)
      constant := (4656324637691578213984206572055820834618785427808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298797188739236268571/50000000000000000000)
  centralHi := (597594377478472537143/100000000000000000000)
  directionLo := (149920057017460203269/25000000000000000000)
  directionHi := (599680228069840813077/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree145.table
  base := (1554640840963736483960941379060781153029/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (7354304830459108235793191956164702000000000000)
      linear := (-1100223890293183945135353291673578780000000000000)
      constant := (42405499296321433930003520825065857896785271536336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree145.table
  base := (124371267277030973571773455011304131782347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1835790450725527974108908107234922550000000000000)
      constant := (70831804281773436394470236268722608885083244965601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149920057017460203269/25000000000000000000)
  centralHi := (599680228069840813077/100000000000000000000)
  directionLo := (601758848611226872857/100000000000000000000)
  directionHi := (300879424305613436429/50000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree146.table
  base := (63455244441738001135272758990687936394021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-5539048223998037522290800480576039420000000000000)
      constant := (215002655245366127170685923736841903756418095208858) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree146.table
  base := (25382097776683635944174729563278524436157/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33672966000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (2451434943486369411931063985388234000000000000)
      linear := (-369689549417688465950832146083084728000000000000)
      constant := (14365136468578527422814954005180354394934441915831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (601758848611226872857/100000000000000000000)
  centralHi := (300879424305613436429/50000000000000000000)
  directionLo := (24153212550745215709/4000000000000000000)
  directionHi := (301915156884315196363/50000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree147.table
  base := (129473949813257712095427471718199084740179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1858992332176718439634944834261394980000000000000)
      constant := (72666199848172341095105894390761002960843583150457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree147.table
  base := (129473949813208506357079246882850915123717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-620368347817118895133137784531974910000000000000)
      constant := (24275501249577460642774737893702238922171634722437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24153212550745215709/4000000000000000000)
  centralHi := (301915156884315196363/50000000000000000000)
  directionLo := (60589469693168284037/10000000000000000000)
  directionHi := (605894696931682840371/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree148.table
  base := (3301541251662729500082795006754233280237/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (7354304830459108235793191956164702000000000000)
      linear := (-1122981153812454623103773704998466092000000000000)
      constant := (44203065875812629553167759758482559819217867675304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree148.table
  base := (26412330013293461783043525993898326498443/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33672966000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (2451434943486369411931063985388234000000000000)
      linear := (-374752467962854208208933195355285164000000000000)
      constant := (14766853699858754238577199197581654013819485095969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60589469693168284037/10000000000000000000)
  centralHi := (605894696931682840371/100000000000000000000)
  directionLo := (607952070243986395327/100000000000000000000)
  directionHi := (9499251097562287427/1562500000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree149.table
  base := (134673589643295028112518590628414293241363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-5652834541594390912132902547200475980000000000000)
      constant := (224052844749007764639838830996785201455345669138987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree149.table
  base := (13467358964325939998598817809699106138859/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33672966000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (2451434943486369411931063985388234000000000000)
      linear := (-377283927235437079337983719991385382000000000000)
      constant := (14969795318915579224768322606594314167744190385794) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (607952070243986395327/100000000000000000000)
  centralHi := (9499251097562287427/1562500000000000000)
  directionLo := (122000500926506385709/20000000000000000000)
  directionHi := (305001252316265964273/50000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree150.table
  base := (2746195370873584470879425070444329510257/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6734593200000000000000000000000000000000000000
      center := (101018898)
      previous := (50509449)
      next := (50509449)
      square := (490286988697273882386212797077646800000000000)
      linear := (-75876844188353449449959154258781620000000000000)
      constant := (3028148608724721398017996501767159512491680612262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree150.table
  base := (27461953708729781783364887613707517836429/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (168364830)
      previous := (84182415)
      next := (84182415)
      square := (817144981162123137310354661796078000000000000)
      linear := (-126605128836006650155678081542495200000000000000)
      constant := (5058041868972389095590595388045213647008411213069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122000500926506385709/20000000000000000000)
  centralHi := (305001252316265964273/50000000000000000000)
  directionLo := (76505758729528747487/12500000000000000000)
  directionHi := (612046069836229979897/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree151.table
  base := (69985093383862481142041533414703312967657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-5728692086658626505360970591616767020000000000000)
      constant := (230190232095105360394824264851561205432941819781986) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree151.table
  base := (139970186767699169855429548935353967006303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1911734228903014107980423846317929090000000000000)
      constant := (76899222819318658447239072740710719646984181352349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76505758729528747487/12500000000000000000)
  centralHi := (612046069836229979897/100000000000000000000)
  directionLo := (122816566886717440821/20000000000000000000)
  directionHi := (307041417216793602053/50000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree152.table
  base := (17831855539436822182541476348729250098839/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-5766620859190744301975004613824912540000000000000)
      constant := (233290104071264679682185762093515801221404427437688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree152.table
  base := (142654844315472633588521914386997354907059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1924391525265928463625676469498430180000000000000)
      constant := (77934760948777413615590959822575482066937665433497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122816566886717440821/20000000000000000000)
  centralHi := (307041417216793602053/50000000000000000000)
  directionLo := (15402821646738984003/2500000000000000000)
  directionHi := (616112865869559360121/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree153.table
  base := (3634093529676236700529969558740793664411/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (168364830)
      previous := (84182415)
      next := (84182415)
      square := (817144981162123137310354661796078000000000000)
      linear := (-128989991816063602190867525245179068000000000000)
      constant := (5253572479618559198677582201199007082499636017368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree153.table
  base := (72681870593515399629229393411400096144843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-645682940542947606423643030892977090000000000000)
      constant := (26325747474321045789393134842073520597460676471446) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15402821646738984003/2500000000000000000)
  centralHi := (616112865869559360121/100000000000000000000)
  directionLo := (618136230481610592159/100000000000000000000)
  directionHi := (3863351440510066201/625000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree154.table
  base := (74048438691225022221027254906319433510343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-5842478404254979895203072658241203580000000000000)
      constant := (239552204629819864469565369188345570569199121462014) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree154.table
  base := (7404843869121708132846845063703628610523/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33672966000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (2451434943486369411931063985388234000000000000)
      linear := (-389941223598351434983236343171886472000000000000)
      constant := (16005333448375369648274576094431223134557536442436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (618136230481610592159/100000000000000000000)
  centralHi := (3863351440510066201/625000000000000000)
  directionLo := (620152993525007488911/100000000000000000000)
  directionHi := (38759562095312968057/6250000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree155.table
  base := (75427126450877844305272676013307757220411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-5880407176787097691817106680449349100000000000000)
      constant := (242714433212221780615833869988943196969257462327078) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree155.table
  base := (150854252901742178315526991111523967528049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1962363414354671530561434339039933450000000000000)
      constant := (81083035405519547240381451276075626445878549011667) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (620152993525007488911/100000000000000000000)
  centralHi := (38759562095312968057/6250000000000000000)
  directionLo := (124432643839475041377/20000000000000000000)
  directionHi := (311081609598687603443/50000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree156.table
  base := (153635867745024725494252504691597847105399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1972778649773071829477046900885831540000000000000)
      constant := (81965815776681286113757390171106064515626649471717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree156.table
  base := (76817933872506616526138062250875480136777/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-658340236905861962068895654073478180000000000000)
      constant := (27382115637964072464624863498121946210959789090194) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124432643839475041377/20000000000000000000)
  centralHi := (311081609598687603443/50000000000000000000)
  directionLo := (78020871332817725183/12500000000000000000)
  directionHi := (124833394132508360293/20000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree157.table
  base := (39110430478078601143171698093008515283691/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-5956264721851333285045174724865640140000000000000)
      constant := (249101246983288989285545899299756503677149244385036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree157.table
  base := (78220860956152314502296310346518377299807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-1987678007080500241851939585400935630000000000000)
      constant := (83216601766995823468314636958109045179691572917562) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78020871332817725183/12500000000000000000)
  centralHi := (124833394132508360293/20000000000000000000)
  directionLo := (78270538759211977701/12500000000000000000)
  directionHi := (626164310073695821609/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree158.table
  base := (79635907701840444667945706216565443956349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-5994193494383451081659208747073785660000000000000)
      constant := (252325832171960010235591055233372971133351136083402) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree158.table
  base := (796359077018362872458730857476238050947/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6734593200000000000000000000000000000000000000
      center := (101018898)
      previous := (50509449)
      next := (50509449)
      square := (490286988697273882386212797077646800000000000)
      linear := (-80013412137736583899887688343257468800000000000)
      constant := (3371751998593252472564537336235091943989778395208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78270538759211977701/12500000000000000000)
  centralHi := (626164310073695821609/100000000000000000000)
  directionLo := (157038824648970297097/25000000000000000000)
  directionHi := (628155298595881188389/100000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree159.table
  base := (40531537054794813355553441333789673453413/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-2010707422305189626091080923093977060000000000000)
      constant := (85190400965353234310178330260666066170695757065916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree159.table
  base := (81063074109586090657277679453651700944189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-670997533268776317714148277253979270000000000000)
      constant := (28459313835799870106722853759859839794745281364858) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157038824648970297097/25000000000000000000)
  centralHi := (628155298595881188389/100000000000000000000)
  directionLo := (15753499910696309773/2500000000000000000)
  directionHi := (630139996427852390921/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree160.table
  base := (41251180089715870548980180479074445503751/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-6070051039447686674887276791490076700000000000000)
      constant := (258837359155590794141380889880622841089499961772796) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree160.table
  base := (165004720358857467322787553192433230879441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-2025649896169243308787697454942438900000000000000)
      constant := (86469026394701628457089325462607269820336783446003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15753499910696309773/2500000000000000000)
  centralHi := (630139996427852390921/100000000000000000000)
  directionLo := (316059231411656046527/50000000000000000000)
  directionHi := (126423692564662418611/20000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree161.table
  base := (167907531822786478757813737037421990320013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (14322150)
      previous := (7161075)
      next := (7161075)
      square := (69511387811522762153054744387190000000000000)
      linear := (-11546275637012862895087544071263180000000000000)
      constant := (495509075520899727740265832651546329057745161253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree161.table
  base := (5247110369461917602152391296976422184787/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 318270000000000000000000000000000000000000000
      center := (4774050)
      previous := (2387025)
      next := (2387025)
      square := (23170462603840920717684914795730000000000000)
      linear := (-3853132689096706359986673115544310000000000000)
      constant := (165533184549599730420773637588376937344006907168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316059231411656046527/50000000000000000000)
  centralHi := (126423692564662418611/20000000000000000000)
  directionLo := (79261344513944043503/12500000000000000000)
  directionHi := (25363630244462093921/4000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree162.table
  base := (170834582611000073544381888166161182372353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-682878731612435807568371648434040860000000000000)
      constant := (29492447586773089595220298928393555467424006984833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree162.table
  base := (85417291305497861562595251571002542560039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-683654829631690673359400900434480360000000000000)
      constant := (29557342067836790055064202691754807810512582068558) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79261344513944043503/12500000000000000000)
  centralHi := (25363630244462093921/4000000000000000000)
  directionLo := (636056933717519763743/100000000000000000000)
  directionHi := (19876779178672492617/3125000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree163.table
  base := (217232340904443796009982709656128784353/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 20203779600000000000000000000000000000000000000
      center := (303056694)
      previous := (151528347)
      next := (151528347)
      square := (1470860966091821647158638391232940400000000000)
      linear := (-247353494281761602589175154324580530400000000000)
      constant := (10750421645871956386639977168223711637462715247904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree163.table
  base := (173785872723551337175837003691113488097129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-2063621785257986375723455324483942170000000000000)
      constant := (89783941125018821904654328023556849035918014757307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (636056933717519763743/100000000000000000000)
  centralHi := (19876779178672492617/3125000000000000000)
  directionLo := (638017052181324146469/100000000000000000000)
  directionHi := (63801705218132414647/10000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree164.table
  base := (176761402160501093386046937255946615682073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-6221766129576157861343412880322658780000000000000)
      constant := (272109839548081777475790559065702700491516266407777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree164.table
  base := (176761402160497947306738785052287298850027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-2076279081620900731368707947664443260000000000000)
      constant := (90902799391264450089391140649199975538204399135041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (638017052181324146469/100000000000000000000)
  centralHi := (63801705218132414647/10000000000000000000)
  directionLo := (159992791794302343249/25000000000000000000)
  directionHi := (639971167177209372997/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree165.table
  base := (179761170921886939264546087149548592281629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-2086564967369425219319148967510268100000000000000)
      constant := (91826641161602956464592178981153995331623577870807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree165.table
  base := (179761170921884264012726986293111976938451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-696312125994605029004653523614981450000000000000)
      constant := (30676200334082691610940397337658613793106874102611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159992791794302343249/25000000000000000000)
  centralHi := (639971167177209372997/100000000000000000000)
  directionLo := (64191933353200449949/10000000000000000000)
  directionHi := (641919333532004499491/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree166.table
  base := (91392589503880129761588267752310258498249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-6297623674640393454571480924738949820000000000000)
      constant := (278870792956982593967058173221248797827588248909602) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree166.table
  base := (182785179007757984720433311314693246056251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-2101593674346729442659213194025445440000000000000)
      constant := (93161345957970499191857110544876446757440887005233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64191933353200449949/10000000000000000000)
  centralHi := (641919333532004499491/100000000000000000000)
  directionLo := (160965401310768101683/25000000000000000000)
  directionHi := (643861605243072406733/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree167.table
  base := (185833426418167747318557482165154266548687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-6335552447172511251185514946947095340000000000000)
      constant := (282282447964605309641248374386004051643373312043463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree167.table
  base := (46458356604541453273289142782208837416159/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-2114250970709643798304465817205946530000000000000)
      constant := (94301034258432509491932064400422246616927699715188) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160965401310768101683/25000000000000000000)
  centralHi := (643861605243072406733/100000000000000000000)
  directionLo := (645798035495772605113/100000000000000000000)
  directionHi := (322899017747886302557/50000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree168.table
  base := (94452956576577561810049017189682898503207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (12257174717431847059655319926941170000000000000)
      linear := (-2124493739901543015933182989718413620000000000000)
      constant := (95238296169226441919106580100139013872079940201962) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree168.table
  base := (188905913153153479040600257348099172010393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (841824150)
      previous := (420912075)
      next := (420912075)
      square := (4085724905810615686551773308980390000000000000)
      linear := (-708969422357519384649906146795482540000000000000)
      constant := (31815888634544958554631122650396254957289019189273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell093.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (645798035495772605113/100000000000000000000)
  centralHi := (322899017747886302557/50000000000000000000)
  directionLo := (647728676680454176669/100000000000000000000)
  directionHi := (64772867668045417667/10000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree169.table
  base := (192002639212767157462035894742486033771911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (7576417350)
      previous := (3788208675)
      next := (3788208675)
      square := (36771524152295541178965959780823510000000000000)
      linear := (-6411409992236746844413582991363386380000000000000)
      constant := (289168114586206903574523879457598751816014616287039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree169.table
  base := (9600131960638287960204598917551187934211/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33672966000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (2451434943486369411931063985388234000000000000)
      linear := (-427913112687094501918994212713389742000000000000)
      constant := (19320248178715670317780306114614386345636594479652) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell093.Kernel169
