import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell044.Parameters
import ForestUnimodality.BinomialMassData.Q4487_9312.Batch000_049
import ForestUnimodality.BinomialMassData.Q4487_9312.Batch050_099
import ForestUnimodality.BinomialMassData.Q4487_9312.Batch100_149
import ForestUnimodality.BinomialMassData.Q4487_9312.Batch150_199
import ForestUnimodality.BinomialMassData.Q8999_18624.Batch000_049
import ForestUnimodality.BinomialMassData.Q8999_18624.Batch050_099
import ForestUnimodality.BinomialMassData.Q8999_18624.Batch100_149
import ForestUnimodality.BinomialMassData.Q8999_18624.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree000.table
  base := (839374196607930135771624689/10000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (42)
      previous := (21)
      next := (21)
      square := (163509306266315240785402807500000000000)
      linear := (7033458248850224525661190000000000000)
      constant := (209843549151982533942906172250000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree000.table
  base := (839374196607930135771624689/10000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (42)
      previous := (21)
      next := (21)
      square := (163509306266315240785402807500000000000)
      linear := (7033458248850224525661190000000000000)
      constant := (209843549151982533942906172250000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree001.table
  base := (120595496670798691980139497911277181606919/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-4249318258387503405076532373213281250000000)
      constant := (3405025022646424534237676604739449327972408863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree001.table
  base := (481390191427611691000450108189084241891593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-17046836792011990427669204718876562500000000)
      constant := (13592127535529036085479108547223505624877901861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (4996705188371811201/10000000000000000000)
  directionHi := (49967051883718112011/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree002.table
  base := (57839204672130990414353706400708646400201/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-34788679771061208391355612626226250000000000)
      constant := (8179516470151537854276355370697870473754868135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree002.table
  base := (144063133424177479154723337490158164456643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-17443903643992581003040881539136562500000000)
      constant := (4074706991793301728040377535933554591125474461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4996705188371811201/10000000000000000000)
  centralHi := (49967051883718112011/100000000000000000000)
  directionLo := (1413281648915085213/2000000000000000000)
  directionHi := (70664082445754260651/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree003.table
  base := (182685602824210380295867409431464585584081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-17526695502857467720801698586533125000000000)
      constant := (1731365403244166567493245484383192658807493129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree003.table
  base := (181805299735054586633435437325266050679557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-17576259261319444528164773812556562500000000)
      constant := (1723153312363375769904594463620923707855670563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1413281648915085213/2000000000000000000)
  centralHi := (70664082445754260651/100000000000000000000)
  directionLo := (21636368141757486827/25000000000000000000)
  directionHi := (86545472567029947309/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree004.table
  base := (7646538225249156238685546482933714689173/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-17592873311520899483363644723243125000000000)
      constant := (880118311103608670103093231463236772187645084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree004.table
  base := (60842294782217365393019810741767556715781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-35284874139965752581453439898533125000000000)
      constant := (1751110594184550182151168155920134405447600287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21636368141757486827/25000000000000000000)
  centralHi := (86545472567029947309/100000000000000000000)
  directionLo := (4996705188371811201/5000000000000000000)
  directionHi := (99934103767436224021/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree005.table
  base := (86863033329857698357072891988026998520289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-88162899983594792704504062026345625000000000)
      constant := (2557129742117807130133806868614895362622822603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree005.table
  base := (86383053326627299111858937681232300915579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-88410718775904676741319438156462812500000000)
      constant := (2544173907303975996689429855351974883041704683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4996705188371811201/5000000000000000000)
  centralHi := (99934103767436224021/100000000000000000000)
  directionLo := (27932431161813153913/25000000000000000000)
  directionHi := (111729724647252615653/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree006.table
  base := (32480348344012363057437440355684274738669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3076918125319520201099710031535000000000000)
      linear := (-17659051120184331245925590859953125000000000)
      constant := (330943384528000937945327465726019337109886621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree006.table
  base := (16152656078643484436976007817747811230053/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1538459062659760100549855015767500000000000)
      linear := (-8854307439323154026644333042988281250000000)
      constant := (164719448412884837698705292313889905375287427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27932431161813153913/25000000000000000000)
  centralHi := (111729724647252615653/100000000000000000000)
  directionLo := (24478756213256478571/20000000000000000000)
  directionHi := (15299222633285299107/12500000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree007.table
  base := (12662417839517949159887664038882171012211/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-30936428364654295561650757073272968750000000)
      constant := (409260907602663442205745534529277981103086147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree007.table
  base := (12597069057442860683084937905829589422069/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-62046329883925509949072277437627968750000000)
      constant := (815414816996588296578358236132832626829186451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24478756213256478571/20000000000000000000)
  centralHi := (15299222633285299107/12500000000000000000)
  directionLo := (132200393031379615791/100000000000000000000)
  directionHi := (8262524564461225987/6250000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree008.table
  base := (40719108401504075298379745430492885513041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-141537120196128377017652511426465000000000000)
      constant := (1420647078858857856409058111631443304376608307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree008.table
  base := (20258527729738956841079076980881536279599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-70966815131912095738278556617326250000000000)
      constant := (708232901396392998447511745822031952689240973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132200393031379615791/100000000000000000000)
  centralHi := (8262524564461225987/6250000000000000000)
  directionLo := (141328164891508521301/100000000000000000000)
  directionHi := (70664082445754260651/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree009.table
  base := (1336942557484509913331339530922726468419/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-53109508977879857262900664853279375000000000)
      constant := (429067336025912230122468790549987190955734275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree009.table
  base := (33261440694710459575684195167335065650043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-53258200253265787684989890531349687500000000)
      constant := (428184442454928732910187707927378315806723337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141328164891508521301/100000000000000000000)
  centralHi := (70664082445754260651/50000000000000000000)
  directionLo := (14990115565115433603/10000000000000000000)
  directionHi := (149901155651154336031/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree010.table
  base := (6948803800052099184979664336915914356979/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-44279983417787691639937869423302812500000000)
      constant := (302347421222100520700732660042735914945071233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree010.table
  base := (13830339170290412147035338308451594571143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-88807785627885267316691114976722812500000000)
      constant := (603986507993133196598317746572377735154965961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14990115565115433603/10000000000000000000)
  centralHi := (149901155651154336031/100000000000000000000)
  directionLo := (39502422979089030541/25000000000000000000)
  directionHi := (31601938383271224433/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree011.table
  base := (23282179365184581125807704788914930469081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-194911340408661961330800960826584375000000000)
      constant := (1171632112772461026643667173598747455241374387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree011.table
  base := (2895941215520056163027550485993052654969/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-97728270875871853105897394156421093750000000)
      constant := (585638981318236079289753046383684068903567977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39502422979089030541/25000000000000000000)
  centralHi := (31601938383271224433/20000000000000000000)
  directionLo := (41430490744628492591/25000000000000000000)
  directionHi := (33144392595702794073/20000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree012.table
  base := (977888211860841122765988589497291407733/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1538459062659760100549855015767500000000000)
      linear := (-17725228928847763008487536996663125000000000)
      constant := (97058979262216913855363643365973316464298985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree012.table
  base := (19458204998784136307807471089231173768329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-71099170749238959263402448890746250000000000)
      constant := (388442850437861647504109859019430606173707561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41430490744628492591/25000000000000000000)
  centralHi := (33144392595702794073/20000000000000000000)
  directionLo := (173090945134059894617/100000000000000000000)
  directionHi := (86545472567029947309/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree013.table
  base := (16419398940051107089422154816432227167059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-230494153883684350872899927093330625000000000)
      constant := (1182898631886805858676044157886373657885199393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree013.table
  base := (510371474686921404560151341838234317637/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-115569241371845024684309952515817656250000000)
      constant := (592228160639614377032118530557103792173111709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173090945134059894617/100000000000000000000)
  centralHi := (86545472567029947309/50000000000000000000)
  directionLo := (180158767650515167581/100000000000000000000)
  directionHi := (90079383825257583791/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree014.table
  base := (13734695198873034351053377034577698784879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-248285560621195545643949410226703750000000000)
      constant := (1222467831159883615967294179495257242663279533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree014.table
  base := (6828612138925385930540779823325005824023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-124489726619831610473516231695515937500000000)
      constant := (612476799533818824011665611470385256777509721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180158767650515167581/100000000000000000000)
  centralHi := (90079383825257583791/50000000000000000000)
  directionLo := (23369948597003832039/12500000000000000000)
  directionHi := (186959588776030656313/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree015.table
  base := (2853086232261496076428551653387986843437/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1538459062659760100549855015767500000000000)
      linear := (-22173080613225561701249907780006406250000000)
      constant := (106736499638399863937250330694123649752867483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree015.table
  base := (5671756462279901595705523551444960393751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1538459062659760100549855015767500000000000)
      linear := (-22235035311303032710453751812535703125000000)
      constant := (107021675130151857354225356261672422495643767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23369948597003832039/12500000000000000000)
  centralHi := (186959588776030656313/100000000000000000000)
  directionLo := (48380389951180546659/25000000000000000000)
  directionHi := (193521559804722186637/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree016.table
  base := (4693080622784180057720480237974355514473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-141934187048108967593024188246725000000000000)
      constant := (678070434093305019284986321081553383107029371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree016.table
  base := (2331229836962574243295331674124496341449/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-71165348557902391025964395027456250000000000)
      constant := (340129384647494537439023414364532314480080923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48380389951180546659/25000000000000000000)
  centralHi := (193521559804722186637/100000000000000000000)
  directionLo := (4996705188371811201/2500000000000000000)
  directionHi := (199868207534872448041/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree017.table
  base := (3803060254487445859045282850192916448157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-150829890416864564978548929813411562500000000)
      constant := (723482215733066225946043840822136004339940139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree017.table
  base := (151032601191981626873779531003353924289/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-75625591181895683920567534617305390625000000)
      constant := (363079956205713115092742470141055060793546600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4996705188371811201/2500000000000000000)
  centralHi := (199868207534872448041/100000000000000000000)
  directionLo := (103009716358643835141/50000000000000000000)
  directionHi := (206019432717287670283/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree018.table
  base := (6033170732131453161442614519905787025053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-106483729190413441576049114253398750000000000)
      constant := (517402121686176877986674545578356479806223677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree018.table
  base := (5984723903662183186555762048524180407527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-106781111741185302420227565609539375000000000)
      constant := (519522777595323096979774838656718495876296543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103009716358643835141/50000000000000000000)
  centralHi := (206019432717287670283/100000000000000000000)
  directionLo := (414047358080591371/195312500000000000)
  directionHi := (211992247337262781953/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree019.table
  base := (2318048165930408827106509598277137264671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-168621297154375759749598412946784687500000000)
      constant := (835492773348730502068102281428131531890180817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree019.table
  base := (1148268251728687837347297742007920719157/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-169092152859764539419547627594007343750000000)
      constant := (839192208002316733991287342841095616484367403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414047358080591371/195312500000000000)
  centralHi := (211992247337262781953/100000000000000000000)
  directionLo := (217801329667780900787/100000000000000000000)
  directionHi := (54450332416945225197/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree020.table
  base := (211845614710770032620266918122632206257/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-88758500261565678567561577256735625000000000)
      constant := (450646482182115367663538453081338008706565356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree020.table
  base := (3351374494022305412275664502454911497389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-356025276215502250417507813547411250000000000)
      constant := (1811053850216778612687819236196723888399299303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217801329667780900787/100000000000000000000)
  centralHi := (54450332416945225197/25000000000000000000)
  directionLo := (27932431161813153913/12500000000000000000)
  directionHi := (44691889858901046261/20000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree021.table
  base := (454524506929790212037078075212467869573/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-124275135927924636347098597386771875000000000)
      constant := (648806338223445290787009077173599330220936785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree021.table
  base := (1119415925212784151664558959248043884541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1538459062659760100549855015767500000000000)
      linear := (-31155520559289618499660030992233984375000000)
      constant := (162999134350495000928910851523913088348377822) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27932431161813153913/12500000000000000000)
  centralHi := (44691889858901046261/20000000000000000000)
  directionLo := (114488898755462020823/50000000000000000000)
  directionHi := (228977797510924041647/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree022.table
  base := (1268108648930753528535762412783609588723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-390616814521285103812345275293688750000000000)
      constant := (2101997443329572938570843017068453299423384121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree022.table
  base := (309556148526029766588943739739919758097/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-97926804301862148393583232566551093750000000)
      constant := (528176404856531810257356477385258111984460269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114488898755462020823/50000000000000000000)
  centralHi := (228977797510924041647/100000000000000000000)
  directionLo := (234366247627306415361/100000000000000000000)
  directionHi := (117183123813653207681/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree023.table
  base := (45201969115282120237879168708023392661/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-102102055314699074645848689606765468750000000)
      constant := (567228881064339352588125962030533614425690344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree023.table
  base := (167610696257456558044825251632622557867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-102387046925855441288186372156400234375000000)
      constant := (570199335338411945706750836990081491737057467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234366247627306415361/100000000000000000000)
  centralHi := (117183123813653207681/50000000000000000000)
  directionLo := (239633562550937525583/100000000000000000000)
  directionHi := (14977097659433595349/6250000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree024.table
  base := (-458862478868433042533403711319037889817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-142066542665435831118148080520145000000000000)
      constant := (815611451634676528132530817923781047494711847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree024.table
  base := (-241072988774337435747261231909872404133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3076918125319520201099710031535000000000000)
      linear := (-71231526366565822788526341164166250000000000)
      constant := (409987825158674703919733553584311494924512603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239633562550937525583/100000000000000000000)
  centralHi := (14977097659433595349/6250000000000000000)
  directionLo := (24478756213256478571/10000000000000000000)
  directionHi := (244787562132564785711/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree025.table
  base := (-1203380845986172903609855740803192436569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-443991034733818688125493724693808125000000000)
      constant := (2635470118442836798571616397155905171858591837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree025.table
  base := (-611948358762068855454621166902815137461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-111307532173842027077392651336098515625000000)
      constant := (662452909055588113357093884520124775417795739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24478756213256478571/10000000000000000000)
  centralHi := (244787562132564785711/100000000000000000000)
  directionLo := (4996705188371811201/2000000000000000000)
  directionHi := (249835259418590560051/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree026.table
  base := (-940187601856816348905033484349277773599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-230891220735664941448271603913590625000000000)
      constant := (1417292347993357562312834514949071549565871027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree026.table
  base := (-1898433433192067783839752818797380675729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-463071099191341279887983163703790625000000000)
      constant := (2850214216811191691399096623422629392306822517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4996705188371811201/2000000000000000000)
  centralHi := (249835259418590560051/100000000000000000000)
  directionLo := (31847871573972721311/12500000000000000000)
  directionHi := (254782972591781770489/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree027.table
  base := (-2496933013031218750687764658880035493269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-159857949402947025889197563653518125000000000)
      constant := (1014659343258190211069448430840219962840706979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree027.table
  base := (-628203163721139359814958354561894827263/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3076918125319520201099710031535000000000000)
      linear := (-80152011614552408577732620343864531250000000)
      constant := (510155918006146994449346950600201962115174241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31847871573972721311/12500000000000000000)
  centralHi := (254782972591781770489/100000000000000000000)
  directionLo := (129818208850544920963/50000000000000000000)
  directionHi := (259636417701089841927/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree028.table
  base := (-1529507765917588934345284183606562878567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-248682627473176136219321087046963750000000000)
      constant := (1631740925689882982857024113910020127751689291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree028.table
  base := (-614593405165682061837264409859968576957/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-498753040183287623044808280422583750000000000)
      constant := (3281808049179060293198391494729033373953673805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129818208850544920963/50000000000000000000)
  centralHi := (259636417701089841927/100000000000000000000)
  directionLo := (264400786062759231583/100000000000000000000)
  directionHi := (8262524564461225987/3125000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree029.table
  base := (-446455184373997038781831270893083551641/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-128789165420965866802422914306825156250000000)
      constant := (873238624384441344766475001669775047210815236) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree029.table
  base := (-1791944471761667262587439929711851978541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-129148502669815198655805209695495078125000000)
      constant := (878172729958375602369151087399117925172150659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264400786062759231583/100000000000000000000)
  centralHi := (8262524564461225987/3125000000000000000)
  directionLo := (269080809320462603013/100000000000000000000)
  directionHi := (134540404660231301507/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree030.table
  base := (-1009759875089068524223061204892243719289/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1538459062659760100549855015767500000000000)
      linear := (-44412339035114555165061761696722812500000000)
      constant := (311023050493608782069722898208506330017084799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree030.table
  base := (-2024891498626033382143150223693010943817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3076918125319520201099710031535000000000000)
      linear := (-89072496862538994366938899523562812500000000)
      constant := (625577572843087417891220874548522435615563347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269080809320462603013/100000000000000000000)
  centralHi := (134540404660231301507/50000000000000000000)
  directionLo := (273680814487434123783/100000000000000000000)
  directionHi := (34210101810929265473/12500000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree031.table
  base := (-446477520685352271924846751286038048161/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-275369737579442928375895311747023437500000000)
      constant := (1990673765187758631899966438433362603080609765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree031.table
  base := (-559274110928587134498094717754585492349/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-276137975835603568890022977750386718750000000)
      constant := (2002015786411269033492164475161688172606812233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273680814487434123783/100000000000000000000)
  centralHi := (34210101810929265473/12500000000000000000)
  directionLo := (5564095415876888411/2000000000000000000)
  directionHi := (278204770793844420551/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree032.table
  base := (-4851857143838702617460407982413810019083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-568530881896397051522840106627420000000000000)
      constant := (4240082348571757983071924669812055384591344159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree032.table
  base := (-972021466262426151470454717005257654387/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-570116922167180309358458513860170000000000000)
      constant := (4264304964603475968566881228168925460948090755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5564095415876888411/2000000000000000000)
  centralHi := (278204770793844420551/100000000000000000000)
  directionLo := (141328164891508521301/50000000000000000000)
  directionHi := (282656329783017042603/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree033.table
  base := (-2601412725792452430570630217741321128773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3076918125319520201099710031535000000000000)
      linear := (-97720381438984707715648264960132187500000000)
      constant := (751401559995423166838446420741654228835312343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree033.table
  base := (-5210048581952305142761951446411281669417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-195985964221051160312290357406522187500000000)
      constant := (1511404805588165876985877496392832879190424197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141328164891508521301/50000000000000000000)
  centralHi := (282656329783017042603/100000000000000000000)
  directionLo := (8969964369026084619/3125000000000000000)
  directionHi := (287038859808834707809/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree034.table
  base := (-5519826078962472329417123189442910631177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-604113695371419441064939072894166250000000000)
      constant := (4786267990879097149227102063575761875676266821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree034.table
  base := (-5526146513246915049273708411123066919719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-605798863159126652515283630578963125000000000)
      constant := (4813699809355092822555432453795737168572716787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8969964369026084619/3125000000000000000)
  centralHi := (287038859808834707809/100000000000000000000)
  directionLo := (9104858620662486421/3125000000000000000)
  directionHi := (291355475861199565473/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree035.table
  base := (-1160934598986792788293402684905628436423/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-621905102108930635835988556027539375000000000)
      constant := (5073607038389526277049529169243113124766064895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree035.table
  base := (-5810200693571438204775156186331990492753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-623639833655099824093696188938359687500000000)
      constant := (5102710345958726933535197506362343684146217319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9104858620662486421/3125000000000000000)
  centralHi := (291355475861199565473/100000000000000000000)
  directionLo := (295609065470354309301/100000000000000000000)
  directionHi := (147804532735177154651/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree036.table
  base := (-3029450193466399364164968786798473887851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3076918125319520201099710031535000000000000)
      linear := (-106616084807740305101173006526818750000000000)
      constant := (895063866165857210918136967811946518564209941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree036.table
  base := (-6063732445687093466199387316000529228671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-213826934717024331890702915765918750000000000)
      constant := (1800401028065939679740759081213296450174934561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295609065470354309301/100000000000000000000)
  centralHi := (147804532735177154651/50000000000000000000)
  directionLo := (14990115565115433603/5000000000000000000)
  directionHi := (299802311302308672061/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree037.table
  base := (-314190324803791360610555491203024113877/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-164371978895988256344521880573571406250000000)
      constant := (1419139955310985693728673348898351291785625855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree037.table
  base := (-3144014273178116003393118613475982032801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-164830443661761541812630326414288203125000000)
      constant := (1427285425556174563262407707758858354166977149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14990115565115433603/5000000000000000000)
  centralHi := (299802311302308672061/100000000000000000000)
  directionLo := (30393771094774760749/10000000000000000000)
  directionHi := (303937710947747607491/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree038.table
  base := (-810061307351268814178302399747347331379/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-168819830580366055037284251356914687500000000)
      constant := (1498026471452858120485996833995650685394954934) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree038.table
  base := (-6484177937739240389601913937538791252581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-677162745143019338828933864016549375000000000)
      constant := (6026495462469003343501588414814939970954021113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30393771094774760749/10000000000000000000)
  centralHi := (303937710947747607491/100000000000000000000)
  directionLo := (308017594319069302059/100000000000000000000)
  directionHi := (15400879715953465103/5000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree039.table
  base := (-664988329417660772606886356339164290757/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3076918125319520201099710031535000000000000)
      linear := (-115511788176495902486697748093505312500000000)
      constant := (1052832518470524436914623429536352038402274435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree039.table
  base := (-1663275647851515913221658242226111372903/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3076918125319520201099710031535000000000000)
      linear := (-115833952606498751734557737062657656250000000)
      constant := (1058873056739871578663957238577182213674945721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308017594319069302059/100000000000000000000)
  centralHi := (15400879715953465103/5000000000000000000)
  directionLo := (312044138999688522121/100000000000000000000)
  directionHi := (156022069499844261061/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree040.table
  base := (-1358554797143098622644421181280308023793/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-710862135796486609691235971694405000000000000)
      constant := (6651205225640693307381890564191219352061974945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree040.table
  base := (-1359116694998282509924940425211644849367/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-712844686134965681985758980735342500000000000)
      constant := (6689348291761951658071607824567895910434588455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312044138999688522121/100000000000000000000)
  centralHi := (156022069499844261061/50000000000000000000)
  directionLo := (316019383832712244329/100000000000000000000)
  directionHi := (31601938383271224433/10000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree041.table
  base := (-6909831449649475434584626608463831110971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-728653542533997804462285454827778125000000000)
      constant := (6994717348765855268546428291174583636496246583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree041.table
  base := (-1382456482727812094791897186700552456381/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-730685656630938853564171539094739062500000000)
      constant := (7034806635098836610168696843696211984635073815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316019383832712244329/100000000000000000000)
  centralHi := (31601938383271224433/10000000000000000000)
  directionLo := (319945240989700121463/100000000000000000000)
  directionHi := (39993155123712515183/12500000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree042.table
  base := (-875202881303190516451901039659547973023/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1538459062659760100549855015767500000000000)
      linear := (-62203745772625749936111244830095937500000000)
      constant := (612292955433532324879774725030969780540528186) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree042.table
  base := (-7003760507462432716290699205150801411943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-249508875708970675047528032484711875000000000)
      constant := (2463199177425660890867632579598575513811903313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319945240989700121463/100000000000000000000)
  centralHi := (39993155123712515183/12500000000000000000)
  directionLo := (64764701344453821077/20000000000000000000)
  directionHi := (161911753361134552693/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree043.table
  base := (-7068630216223416210195566604341563052651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-764236356009020194004384421094524375000000000)
      constant := (7709585985677060631869472606345583287603445223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree043.table
  base := (-3535246828756108851604055757223489538211/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-191591899405721299180249163953383046875000000)
      constant := (1938426887509358015789215271029204449958123114) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64764701344453821077/20000000000000000000)
  centralHi := (161911753361134552693/50000000000000000000)
  directionLo := (65531174193617999663/20000000000000000000)
  directionHi := (81913967742022499579/25000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree044.table
  base := (-355563080839278290500383174960544465019/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-195506940686632847193858476056974375000000000)
      constant := (2020229343667263586140538316722067658492043435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree044.table
  base := (-7112885662307186949341138309169026933789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-784208568118858368299409214172928750000000000)
      constant := (8127125290359395418287142369815063728302437897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65531174193617999663/20000000000000000000)
  centralHi := (81913967742022499579/25000000000000000000)
  directionLo := (331443925957027940729/100000000000000000000)
  directionHi := (33144392595702794073/10000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree045.table
  base := (-89123303634284422117763063525093790861/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1538459062659760100549855015767500000000000)
      linear := (-66651597457003548628873615613439218750000000)
      constant := (705124986359911498825890125399671959322495770) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree045.table
  base := (-17828198179211008271487240109170193081/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3076918125319520201099710031535000000000000)
      linear := (-133674923102471923312970295422054218750000000)
      constant := (1418306846407203660802760312288915819478533575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331443925957027940729/100000000000000000000)
  centralHi := (33144392595702794073/10000000000000000000)
  directionLo := (83797293485439461739/25000000000000000000)
  directionHi := (335189173941757846957/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree046.table
  base := (-7124733046920416721395600609623180755961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-817610576221553778317532870494643750000000000)
      constant := (8851325049057995956076498526014677765863988853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree046.table
  base := (-3562982760980973367876563283540162308379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-409945254555402355728117165445860937500000000)
      constant := (4450923349603380629930719457348271999654198467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83797293485439461739/25000000000000000000)
  centralHi := (335189173941757846957/100000000000000000000)
  directionLo := (338893034159317260209/100000000000000000000)
  directionHi := (33889303415931726021/10000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree047.table
  base := (-3548059205892696895025604555813578495267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-417700991479532486544291176814008437500000000)
      constant := (4625192970637824393551536252588231296571910891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree047.table
  base := (-3548595812022025657304741691911714313489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-209432869901694470758661722312779609375000000)
      constant := (2325783793656954871984632508808753424943799561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338893034159317260209/100000000000000000000)
  centralHi := (33889303415931726021/10000000000000000000)
  directionLo := (342556849115089732303/100000000000000000000)
  directionHi := (21409803069693108269/6250000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree048.table
  base := (-1761058337870094939560438649685850229677/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1538459062659760100549855015767500000000000)
      linear := (-71099449141381347321635986396782500000000000)
      constant := (804889708464715552779565571525892710188969107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree048.table
  base := (-1761291908093163243492006019146953106961/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1538459062659760100549855015767500000000000)
      linear := (-71297704175229254551088287300876250000000000)
      constant := (809475047958305343632123591830191786966603951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342556849115089732303/100000000000000000000)
  centralHi := (21409803069693108269/6250000000000000000)
  directionLo := (173090945134059894617/50000000000000000000)
  directionHi := (69236378053623957847/20000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree049.table
  base := (-6969258960343960948459631518496224668651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-870984796434087362630681319894763125000000000)
      constant := (10076191618210914218706648767347158794793613223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree049.table
  base := (-3485036043042336878877504156185482472631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-218353355149681056547868001492477890625000000)
      constant := (2533384465549519317067097895814517277717248944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173090945134059894617/50000000000000000000)
  centralHi := (69236378053623957847/20000000000000000000)
  directionLo := (34976936318602678407/10000000000000000000)
  directionHi := (349769363186026784071/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree050.table
  base := (-1717837319307201811400813420583148380529/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-222194050792899639350432700757034062500000000)
      constant := (2625731735780984307579407676407521980428432917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree050.table
  base := (-6872056783166144775277874318183220352049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-891254391094697397769884564329308125000000000)
      constant := (10562642749921307221864834420288495998888337877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34976936318602678407/10000000000000000000)
  centralHi := (349769363186026784071/100000000000000000000)
  directionLo := (353320412228771303253/100000000000000000000)
  directionHi := (176660206114385651627/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree051.table
  base := (-3375317682657762814597396026856946795483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3076918125319520201099710031535000000000000)
      linear := (-151094601651518292028796714360251562500000000)
      constant := (1823146462799209445829460058895645892874737953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree051.table
  base := (-1687812705701114303781495401459789232269/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3076918125319520201099710031535000000000000)
      linear := (-151515893598445094891382853781450781250000000)
      constant := (1833501932431098582215749960352265334420521333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353320412228771303253/100000000000000000000)
  centralHi := (176660206114385651627/50000000000000000000)
  directionLo := (178418062406430044731/50000000000000000000)
  directionHi := (356836124812860089463/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree052.table
  base := (-6607228769650302478247891675521529767161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-924359016646620946943829769294882500000000000)
      constant := (11384043970642853849763619551953107685512346453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree052.table
  base := (-1321552805940188976405960496426689003553/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-926936332086643740926709681048101250000000000)
      constant := (11448641296172085533251260566929463974046047345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178418062406430044731/50000000000000000000)
  centralHi := (356836124812860089463/100000000000000000000)
  directionLo := (180158767650515167581/50000000000000000000)
  directionHi := (360317535301030335163/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree053.table
  base := (-3220612224312996044984178592420243752093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-471075211692066070857439626214127812500000000)
      constant := (5919209922138086828215490026938393511054983389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree053.table
  base := (-3220844928065273549190873937478230682661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-236194325645654228126280559851874453125000000)
      constant := (2976382304200106157370486562868637559253428039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180158767650515167581/50000000000000000000)
  centralHi := (360317535301030335163/100000000000000000000)
  directionLo := (363765628556848976339/100000000000000000000)
  directionHi := (18188281427842448817/5000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree054.table
  base := (-1563175815127374945314422147939405551391/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1538459062659760100549855015767500000000000)
      linear := (-79995152510136944707160727963469062500000000)
      constant := (1025167009609076346549888601530015974963837081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree054.table
  base := (-6253107842452551571802002831193882354861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-320872757692863361361178265922298125000000000)
      constant := (4123891037095295722621187284143469602719987851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363765628556848976339/100000000000000000000)
  centralHi := (18188281427842448817/5000000000000000000)
  directionLo := (73436268639769435713/20000000000000000000)
  directionHi := (183590671599423589283/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree055.table
  base := (-1510433518354881136027097329982237506459/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-244433309214788632814244554673750468750000000)
      constant := (3193698709950173709954924162815945837471588057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree055.table
  base := (-241683428164461802272385134821992221229/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-980459243574563255661947356126290937500000000)
      constant := (12847071068224618798076297834393852126100631675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73436268639769435713/20000000000000000000)
  centralHi := (183590671599423589283/50000000000000000000)
  directionLo := (74113114916932151549/20000000000000000000)
  directionHi := (185282787292330378873/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree056.table
  base := (-1161675111296707974778459338980346083649/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-995524643596665726028027701828375000000000000)
      constant := (13256790361698048505740219500399339480484198385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree056.table
  base := (-5808681102525452128150643638617903804989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-998300214070536427240359914485687500000000000)
      constant := (13331721460007775763148798314942207585546575497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74113114916932151549/20000000000000000000)
  centralHi := (185282787292330378873/50000000000000000000)
  directionLo := (2991353420416490501/800000000000000000)
  directionHi := (186959588776030656313/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree057.table
  base := (-2776338850461275778710271728829307873683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3076918125319520201099710031535000000000000)
      linear := (-168886008389029486799846197493624687500000000)
      constant := (2291331544983130304335985653647857127177454153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree057.table
  base := (-1388235787077155258705341480371998795323/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3076918125319520201099710031535000000000000)
      linear := (-169356864094418266469795412140847343750000000)
      constant := (2304270483398341142509440707673502982284846161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2991353420416490501/800000000000000000)
  centralHi := (186959588776030656313/50000000000000000000)
  directionLo := (47155371117581897757/12500000000000000000)
  directionHi := (377242968940655182057/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree058.table
  base := (-5274683112252437486585868931698483294577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1031107457071688115570126668095121250000000000)
      constant := (14248390361776998115392323562842790388606475021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree058.table
  base := (-5274913677747738810646452483497233288063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1033982155062482770397185031204480625000000000)
      constant := (14328774208458567758896067027089838215118470699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47155371117581897757/12500000000000000000)
  centralHi := (377242968940655182057/100000000000000000000)
  directionLo := (380537729915326934979/100000000000000000000)
  directionHi := (19026886495766346749/5000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree059.table
  base := (-497442810842258784190497498962248864739/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-524449431904599655170588075614247187500000000)
      constant := (7378996306092969968622001739754184769170373735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree059.table
  base := (-994925667421555453182135421648343430703/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1051823125558455941975597589563877187500000000)
      constant := (14841174378026217115378158348499101462505388345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380537729915326934979/100000000000000000000)
  centralHi := (19026886495766346749/5000000000000000000)
  directionLo := (191902104055075752199/50000000000000000000)
  directionHi := (383804208110151504399/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree060.table
  base := (-1162985913336203213946890232180328624793/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1538459062659760100549855015767500000000000)
      linear := (-88890855878892542092685469530155625000000000)
      constant := (1273066262258939052011727090818271342656822663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree060.table
  base := (-4652117504002796893439327509276235259919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-356554698684809704518003382641091250000000000)
      constant := (5120940850541360946323979604659432207126922129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191902104055075752199/50000000000000000000)
  centralHi := (383804208110151504399/100000000000000000000)
  directionLo := (387043119609444373273/100000000000000000000)
  directionHi := (193521559804722186637/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree061.table
  base := (-4307256150738086257389616965378337014643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1084481677284221699883275117495240625000000000)
      constant := (15804797221243208704629602257937596550228297039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree061.table
  base := (-4307407070562283250805779084452880119151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1087505066550402285132422706282670312500000000)
      constant := (15893717998395025940843784756172252676411880973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387043119609444373273/100000000000000000000)
  centralHi := (193521559804722186637/50000000000000000000)
  directionLo := (39025515078082036927/10000000000000000000)
  directionHi := (390255150780820369271/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree062.table
  base := (-3940388119393752897191735053387232994641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1102273084021732894654324600628613750000000000)
      constant := (16341998198955836887616119314783656738322768493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree062.table
  base := (-1970259554661960887567335295654031294653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-552673018523187728355417632321033437500000000)
      constant := (8216930047648762587079989498435994679153642269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39025515078082036927/10000000000000000000)
  centralHi := (390255150780820369271/100000000000000000000)
  directionLo := (98360239993388277049/25000000000000000000)
  directionHi := (393440959973553108197/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree063.table
  base := (-3551358767739204317813242083571429453941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-373354830253081363141791361253995625000000000)
      constant := (5629465846016291064008920173403387933939744131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree063.table
  base := (-443934054947034795259513899597750173797/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3076918125319520201099710031535000000000000)
      linear := (-187197834590391438048207970500243906250000000)
      constant := (2830541385186587031564000984103714185542960483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98360239993388277049/25000000000000000000)
  centralHi := (393440959973553108197/100000000000000000000)
  directionLo := (3172809432753110779/800000000000000000)
  directionHi := (24787573693383677961/6250000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree064.table
  base := (-3140184482851714354300669870690621853393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1137855897496755284196423566895360000000000000)
      constant := (17443994775964287409319667420681895816944275789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree064.table
  base := (-62805662183317126476563435851173294373/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-570513989019160899933830190680430000000000000)
      constant := (8770941096439226868761225266181788285493333225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3172809432753110779/800000000000000000)
  centralHi := (24787573693383677961/6250000000000000000)
  directionLo := (4996705188371811201/1250000000000000000)
  directionHi := (399736415069744896081/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree065.table
  base := (-541375849353854840578089483651849635633/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1155647304234266478967473050028733125000000000)
      constant := (18008789518031093161998674334716650742690561545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree065.table
  base := (-169185300280857396664444184710311596037/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-579434474267147485723036469860128281250000000)
      constant := (9054880677124138511065404607079296297381261933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4996705188371811201/1250000000000000000)
  centralHi := (399736415069744896081/100000000000000000000)
  directionLo := (40284725120914198957/10000000000000000000)
  directionHi := (402847251209141989571/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree066.table
  base := (-2251454990995676333939940536559832378113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-391146236990592557912840844387368750000000000)
      constant := (6194260475819577633334334632529194591841834783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree066.table
  base := (-225152919949123100629679730889640489017/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3076918125319520201099710031535000000000000)
      linear := (-196118319838378023837414249679942187500000000)
      constant := (3114480910951488559812273332607046995030132735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40284725120914198957/10000000000000000000)
  centralHi := (402847251209141989571/100000000000000000000)
  directionLo := (405934248469763548607/100000000000000000000)
  directionHi := (6342722632340055447/1562500000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree067.table
  base := (-1773921898447157894565987883468054932757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1191230117709288868509572016295479375000000000)
      constant := (19165970216814029997380989104498838082553693161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree067.table
  base := (-177398625272703137227319746398942617239/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-298637722381560328650724514109762421875000000)
      constant := (4818313561539974957297908865503640678991775930) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405934248469763548607/100000000000000000000)
  centralHi := (6342722632340055447/1562500000000000000)
  directionLo := (408997946638686570839/100000000000000000000)
  directionHi := (10224948665967164271/2500000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree068.table
  base := (-19910760323294918867832757830774644749/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-302255381111700015820155374857213125000000000)
      constant := (4939588910190029585975131188442659749705219632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree068.table
  base := (-637172230205704310775477081851856365537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-606195930011107243090655307399223125000000000)
      constant := (9934433727889327300242940313829544857401237101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408997946638686570839/100000000000000000000)
  centralHi := (10224948665967164271/2500000000000000000)
  directionLo := (103009716358643835141/25000000000000000000)
  directionHi := (82407773086915068113/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree069.table
  base := (-94070337142750754899709688447475603803/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1538459062659760100549855015767500000000000)
      linear := (-102234410932025938170972581880185468750000000)
      constant := (1696661457489097140239913567748132364536853896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree069.table
  base := (-376305535945365942762202132081314014023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1538459062659760100549855015767500000000000)
      linear := (-102519402543182304813310264429820234375000000)
      constant := (1706143740828157975940375628844839065520833484) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103009716358643835141/25000000000000000000)
  centralHi := (82407773086915068113/20000000000000000000)
  directionLo := (51882188192119801537/12500000000000000000)
  directionHi := (415057505536958412297/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree070.table
  base := (-52187585470818013411901108686012380551/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-311151084480455613205680116423899687500000000)
      constant := (5242678896337254765943950122932660797674811923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree070.table
  base := (-26099034153793189794417609654415127301/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-312018450253540207334533932879309843750000000)
      constant := (5271956593505889171625647820820692365688505596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51882188192119801537/12500000000000000000)
  centralHi := (415057505536958412297/100000000000000000000)
  directionLo := (209027174774305625933/50000000000000000000)
  directionHi := (418054349548611251867/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree071.table
  base := (178571498539900580939898863091461764739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-631197872329666823796884974414485937500000000)
      constant := (10795344887273953252274760639452238946116100253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree071.table
  base := (357106656358288471608536058953796426141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1265914771510134000916548289876635937500000000)
      constant := (21711171759019335588030501312939753970412088257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (209027174774305625933/50000000000000000000)
  centralHi := (418054349548611251867/100000000000000000000)
  directionLo := (105257465724070678189/25000000000000000000)
  directionHi := (421029862896282712757/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree072.table
  base := (37804508081437754701068472705379213187/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-426729050465614947454939810654115000000000000)
      constant := (7406619975707230664751052856530819700421912075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree072.table
  base := (189016242240980947323133583401958581871/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-427918580668702390831653616078677500000000000)
      constant := (7447920305914559278632418129911181860234121195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105257465724070678189/25000000000000000000)
  centralHi := (421029862896282712757/100000000000000000000)
  directionLo := (414047358080591371/97656250000000000)
  directionHi := (84796898934905112781/20000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree073.table
  base := (1555154829777787172377686332575225805457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1297978558134356037135868915095718125000000000)
      constant := (22858225931765461131202841914105498721076259739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree073.table
  base := (777563772773487189446403489659534060259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-325399178125520086018343351648857265625000000)
      constant := (5746398435410561131726351262584766299413566959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414047358080591371/97656250000000000)
  centralHi := (84796898934905112781/20000000000000000000)
  directionLo := (426918678436962949877/100000000000000000000)
  directionHi := (213459339218481474939/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree074.table
  base := (136704125802753432852402055295485472921/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-328942491217966807976729599557272812500000000)
      constant := (5876446923356471118372525233541036199167189268) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree074.table
  base := (87489695066181524215271683051708635759/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1319437682998053515651785964954825625000000000)
      constant := (23636670138053417100089800579422326766929857325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426918678436962949877/100000000000000000000)
  centralHi := (213459339218481474939/50000000000000000000)
  directionLo := (107458208234734548741/25000000000000000000)
  directionHi := (85966566587787638993/20000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree075.table
  base := (2841443375275632416446143405285426823983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-444520457203126142225989293787488125000000000)
      constant := (8054181710307754696723803715470063735283731047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree075.table
  base := (355177862778624027779173746315849906143/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3076918125319520201099710031535000000000000)
      linear := (-222879775582337781205033087219037031250000000)
      constant := (4049498337979452144830693111731854893229707323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107458208234734548741/25000000000000000000)
  centralHi := (85966566587787638993/20000000000000000000)
  directionLo := (432727362835149736543/100000000000000000000)
  directionHi := (13522730088598429267/3125000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree076.table
  base := (1758842230370904309019157108346288947139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-675676389173444810724508682247918750000000000)
      constant := (12414249087461376500547173679768637651235892553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree076.table
  base := (3517666729962245107962371388263679236539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1355119623989999858808611081673618750000000000)
      constant := (24966553343584451331388815756535116100372286353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432727362835149736543/100000000000000000000)
  centralHi := (13522730088598429267/3125000000000000000)
  directionLo := (217801329667780900787/50000000000000000000)
  directionHi := (17424106373422472063/4000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree077.table
  base := (843197434242331305535179800061918773487/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1369144185084400816220066847629210625000000000)
      constant := (25503646766203232229752594513109156337736712745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree077.table
  base := (4215971817457621601072284198718465424541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1372960594485973030387023640033015312500000000)
      constant := (25645360027525901537520211483558621887698675057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217801329667780900787/50000000000000000000)
  centralHi := (17424106373422472063/4000000000000000000)
  directionLo := (109614775205650220343/25000000000000000000)
  directionHi := (438459100822600881373/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree078.table
  base := (4936349714616426813303838487469460841171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-462311863940637336997038776920861250000000000)
      constant := (8729330284726659062916744816383056836742077939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree078.table
  base := (2468168210490769740714619667913345487157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3076918125319520201099710031535000000000000)
      linear := (-231800260830324366994239366398735312500000000)
      constant := (4388901671746782610341771094132307502649597713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109614775205650220343/25000000000000000000)
  centralHi := (438459100822600881373/100000000000000000000)
  directionLo := (441297053432394745027/100000000000000000000)
  directionHi := (110324263358098686257/25000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree079.table
  base := (5678770560179213067103776801489336260027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1404726998559423205762165813895956875000000000)
      constant := (26881530395643748140913778436326191223127407129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree079.table
  base := (709844881467811814167677334362101598267/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-704321267738959686771924378375904218750000000)
      constant := (13515351655212357957459594025017558648946583561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441297053432394745027/100000000000000000000)
  centralHi := (110324263358098686257/25000000000000000000)
  directionLo := (27757304475161356301/6250000000000000000)
  directionHi := (444116871602581700817/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree080.table
  base := (6443248400284124163611479173330161003683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1422518405296934400533215297029330000000000000)
      constant := (27584265353684471327444747519814552954650960041) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree080.table
  base := (6443238438587344477846767460667234684431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1426483505973892545122261315111205000000000000)
      constant := (27737239831477122550711254019705669658437433837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27757304475161356301/6250000000000000000)
  centralHi := (444116871602581700817/100000000000000000000)
  directionLo := (27932431161813153913/6250000000000000000)
  directionHi := (446918898589010462609/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree081.table
  base := (1807445529480989140256750037190652858023/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1538459062659760100549855015767500000000000)
      linear := (-120025817669537132942022065013558593750000000)
      constant := (2358016308064365367830729553273143715534107157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree081.table
  base := (7229773496169423675786986164674005689427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-481441492156621905566891291156867187500000000)
      constant := (9484339854333945078912227717671850051074787393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27932431161813153913/6250000000000000000)
  centralHi := (446918898589010462609/100000000000000000000)
  directionLo := (44970346695346300809/10000000000000000000)
  directionHi := (449703466953463008091/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree082.table
  base := (401918537945364614397647040581394857337/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-364525304692989197518828565824019062500000000)
      constant := (7254330349493381561351791353877322985455882495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree082.table
  base := (4019181648891503406831590155921299443743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-731082723482919444139543215914999062500000000)
      constant := (14589021239420365732567941077808415055531346161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44970346695346300809/10000000000000000000)
  centralHi := (449703466953463008091/100000000000000000000)
  directionLo := (226235449512181099693/50000000000000000000)
  directionHi := (452470899024362199387/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree083.table
  base := (2217253377031695951646317994083052285663/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-368973156377366996211590936607362343750000000)
      constant := (7436910608569965430702596379171874643527565751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree083.table
  base := (4434503526088884935718496272584883799801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-370001604365453014964374747547348671875000000)
      constant := (7478077139164797084948807078598344721986030476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226235449512181099693/50000000000000000000)
  centralHi := (452470899024362199387/100000000000000000000)
  directionLo := (455221507332270880747/100000000000000000000)
  directionHi := (113805376833067720187/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree084.table
  base := (303803427165415202493943418397361103747/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1538459062659760100549855015767500000000000)
      linear := (-124473669353914931634784435796901875000000000)
      constant := (2540596565503103096708874223510847532188744184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree084.table
  base := (2430426020942074640844479702999934495407/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1538459062659760100549855015767500000000000)
      linear := (-124820615663148769286325962379065937500000000)
      constant := (2554651481448954697639283890954240162964159463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455221507332270880747/100000000000000000000)
  centralHi := (113805376833067720187/25000000000000000000)
  directionLo := (457955595021848083293/100000000000000000000)
  directionHi := (228977797510924041647/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree085.table
  base := (10596458647628145976173462301220738771913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1511475438984490374388462712696195625000000000)
      constant := (31235870436456835482681861064526010381205413251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree085.table
  base := (2119290763148006019966542535748488203137/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1515688358453758403014324106908187812500000000)
      constant := (31408570124743790896900875099708392435772396745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457955595021848083293/100000000000000000000)
  centralHi := (228977797510924041647/50000000000000000000)
  directionLo := (460673456241799443547/100000000000000000000)
  directionHi := (115168364060449860887/25000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree086.table
  base := (11493259935080619375944702338889760879049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1529266845722001569159512195829568750000000000)
      constant := (31993777371197908368940928267215079131895416123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree086.table
  base := (2873313938906634144379952132292377770137/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-383382332237432893648184166316896093750000000)
      constant := (8042641396206835513764426196629158063040313349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460673456241799443547/100000000000000000000)
  centralHi := (115168364060449860887/25000000000000000000)
  directionLo := (463375376514241728023/100000000000000000000)
  directionHi := (57921922064280216003/12500000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree087.table
  base := (1241211309770103944509471370422042760747/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3076918125319520201099710031535000000000000)
      linear := (-257843042076585460655093613160490312500000000)
      constant := (5460146596335226427044810514736880367890280115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree087.table
  base := (124121094829956832011379720969059237197/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3076918125319520201099710031535000000000000)
      linear := (-258561716574284124361858203937830156250000000)
      constant := (5490300690961761996212487968706438931567063025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463375376514241728023/100000000000000000000)
  centralHi := (57921922064280216003/12500000000000000000)
  directionLo := (116515408271198583927/25000000000000000000)
  directionHi := (466061633084794335709/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree088.table
  base := (13353017764854565005886156159921839631077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1564849659197023958701611162096315000000000000)
      constant := (33537177046435276400741673625266609392266410479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree088.table
  base := (13353014638935547744084806979328342094707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1569211269941677917749561781986377500000000000)
      constant := (33722285797442473834862238333617547518557294489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116515408271198583927/25000000000000000000)
  centralHi := (466061633084794335709/100000000000000000000)
  directionLo := (234366247627306415361/50000000000000000000)
  directionHi := (468732495254612830723/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree089.table
  base := (7157986810003296655646773528103512367249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-791320532967267576736330322614844062500000000)
      constant := (17161334883767419826309535789497761910973150023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree089.table
  base := (7157985458538225297956599710448288298037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-396763060109412772331993585086443515625000000)
      constant := (8628002632798787670363886417668935276879696762) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234366247627306415361/50000000000000000000)
  centralHi := (468732495254612830723/100000000000000000000)
  directionLo := (235694112347745026143/50000000000000000000)
  directionHi := (471388224695490052287/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree090.table
  base := (612039215714013211618755317042248502623/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-533477490890682116081236709454353750000000000)
      constant := (11705785911226699480554410118581486146216995175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree090.table
  base := (7650489027962095676044807730920730340081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3076918125319520201099710031535000000000000)
      linear := (-267482201822270710151064483117528437500000000)
      constant := (5885163056607900953706013626721801682043259629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235694112347745026143/50000000000000000000)
  centralHi := (471388224695490052287/100000000000000000000)
  directionLo := (237014537874534183247/50000000000000000000)
  directionHi := (94805815149813673299/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree091.table
  base := (101925236578628945751663818605211045053/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-404555969852389385753689902874108593750000000)
      constant := (8980310234589028987649152286508921786846097490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree091.table
  base := (4077008958078154027559161940574375630431/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-811367090714798716242399728532283593750000000)
      constant := (18059594608249963965500719762800185617514179799) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237014537874534183247/50000000000000000000)
  centralHi := (94805815149813673299/20000000000000000000)
  directionLo := (11916382392778286391/2500000000000000000)
  directionHi := (476655295711131455641/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree092.table
  base := (17337145802146897847758712552654390745537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1636015286147068737785809094629807500000000000)
      constant := (36734319376000744934065742639669535643824272899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree092.table
  base := (17337144055811798017425318673222574302239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1640575151925570604063212015423963750000000000)
      constant := (36936643156377451762473992714384912393891800253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11916382392778286391/2500000000000000000)
  centralHi := (476655295711131455641/100000000000000000000)
  directionLo := (479267125101875051167/100000000000000000000)
  directionHi := (14977097659433595349/3125000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree093.table
  base := (18388304073342274727677124891649517351461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-551268897628193310852286192587726875000000000)
      constant := (12518864347288670163961705118888913306806771549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree093.table
  base := (18388302563952123934749438602936140729989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-552805374140514591880541524594453437500000000)
      constant := (12587780051564649148860612104360022366390185251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479267125101875051167/100000000000000000000)
  centralHi := (14977097659433595349/3125000000000000000)
  directionLo := (240932398961496318151/50000000000000000000)
  directionHi := (481864797922992636303/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree094.table
  base := (19461512522607261728245244613106919791021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1671598099622091127327908060896553750000000000)
      constant := (38388061931899658611012380404199935939003649767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree094.table
  base := (19461511218145056430387146358728764203501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1676257092917516947220037132142756875000000000)
      constant := (38599280207537476337236934645799226055687847727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240932398961496318151/50000000000000000000)
  centralHi := (481864797922992636303/100000000000000000000)
  directionLo := (30278033868897116413/6250000000000000000)
  directionHi := (484448541902353862609/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree095.table
  base := (20556771027443660007890430762296152826761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1689389506359602322098957544029926875000000000)
      constant := (39228726042643932632746466846039947421856607747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree095.table
  base := (20556769900198805276804657236828992519817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1694098063413490118798449690502153437500000000)
      constant := (39444463311571838771686691571709032482110780709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30278033868897116413/6250000000000000000)
  centralHi := (484448541902353862609/100000000000000000000)
  directionLo := (97403715745399956267/20000000000000000000)
  directionHi := (60877322340874972667/12500000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree096.table
  base := (21674079483349971565533834213414691408773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-569060304365704505623335675721100000000000000)
      constant := (13359528457049689591003640669304248831465145157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree096.table
  base := (10837039254671020530394563241930878933919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3076918125319520201099710031535000000000000)
      linear := (-285323172318243881729477041476925000000000000)
      constant := (6716481577325427072430724686992661389889243871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97403715745399956267/20000000000000000000)
  centralHi := (60877322340874972667/12500000000000000000)
  directionLo := (24478756213256478571/5000000000000000000)
  directionHi := (489575124265129571421/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree097.table
  base := (36501500481923745522820719732849715021/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (504)
      previous := (252)
      next := (252)
      square := (1962111675195782889424833690000000000000)
      linear := (-183332162805252918656717665033125000000000)
      constant := (4350902318514121369330978755172384231289375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree097.table
  base := (2281343695968149417367793668350011927761/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7500000000000000000000000000000000000000
      center := (126)
      previous := (63)
      next := (63)
      square := (490527918798945722356208422500000000000)
      linear := (-45960782346833788446043012201640625000000)
      constant := (1093701739352086778740731868283807340434770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24478756213256478571/5000000000000000000)
  centralHi := (489575124265129571421/100000000000000000000)
  directionLo := (492118388777707878291/100000000000000000000)
  directionHi := (123029597194426969573/25000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree098.table
  base := (23974845905016201254513221265277539196431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1742763726572135906412105993430046250000000000)
      constant := (41805889671750013835592391912295518512960157837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree098.table
  base := (1498427823626882993103407677927572401811/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-436905243725352408383421841395085781250000000)
      constant := (10508867726103428749083144202521870995622582638) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492118388777707878291/100000000000000000000)
  centralHi := (123029597194426969573/25000000000000000000)
  directionLo := (247324288560139912277/50000000000000000000)
  directionHi := (98929715424055964911/20000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree099.table
  base := (25158303730033239500971421839643731314887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-586851711103215700394385158854473125000000000)
      constant := (14227778213291024495799653824439972115988646783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree099.table
  base := (25158303102051829214920005169556763954093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-588487315132460935037366641313246562500000000)
      constant := (14305875396222910649349187929264510497805779787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247324288560139912277/50000000000000000000)
  centralHi := (98929715424055964911/20000000000000000000)
  directionLo := (248582944467770955547/50000000000000000000)
  directionHi := (99433177787108382219/20000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree100.table
  base := (26363811221086367913360206624802781902039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1778346540047158295954204959696792500000000000)
      constant := (43569974817711345532751566675113593280998854853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree100.table
  base := (6590952669669114945158379447554628208253/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-445825728973338994172628120574784062500000000)
      constant := (10952256128380544516023468601794243875199982431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248582944467770955547/50000000000000000000)
  centralHi := (99433177787108382219/20000000000000000000)
  directionLo := (4996705188371811201/1000000000000000000)
  directionHi := (499670518837181120101/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree101.table
  base := (27591368331202279614385892676396752727593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1796137946784669490725254442830165625000000000)
      constant := (44465810203938914438424838729206157789632392611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree101.table
  base := (86223024571080783516717967041921499981/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-900571943194664574134462520329266406250000000)
      constant := (22354832938849686856009745933715657443218018045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4996705188371811201/1000000000000000000)
  centralHi := (499670518837181120101/100000000000000000000)
  directionLo := (50216265658546131113/10000000000000000000)
  directionHi := (502162656585461311131/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree102.table
  base := (5768195004081410645175830358799933555473/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-604643117840726895165434641987846250000000000)
      constant := (15123613599142478775225730669494728616304727285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree102.table
  base := (28840974615857080271797875985894218666913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-606328285628434106615779199672643125000000000)
      constant := (15206516760038773206272464204872725138983859417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50216265658546131113/10000000000000000000)
  centralHi := (502162656585461311131/100000000000000000000)
  directionLo := (504642487255005241927/100000000000000000000)
  directionHi := (63080310906875655241/12500000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree103.table
  base := (1882039453419081108037551152282660327903/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-457930190064922970066838352274227968750000000)
      constant := (11571266649304330823052140646804839833494278174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree103.table
  base := (1882039431585892841556113860909245202333/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-918412913690637745712875078688662968750000000)
      constant := (23269338859925901640427265677203170240830731853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504642487255005241927/100000000000000000000)
  centralHi := (63080310906875655241/12500000000000000000)
  directionLo := (507110191395192042791/100000000000000000000)
  directionHi := (63388773924399005349/12500000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree104.table
  base := (1570316850260381133230644140937353182991/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-462378041749300768759600723057571250000000000)
      constant := (11802121900623278628390683565801079747731434785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree104.table
  base := (31406336703584453854868426086890243318071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1854666797877248663004162715736722500000000000)
      constant := (47467048196123569495710935262799934804389190117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507110191395192042791/100000000000000000000)
  centralHi := (63388773924399005349/12500000000000000000)
  directionLo := (509565945183563540977/100000000000000000000)
  directionHi := (254782972591781770489/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree105.table
  base := (32722092247384886507836259756526225029879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-622434524578238089936484125121219375000000000)
      constant := (16047034604187475303961024232982049733728006511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree105.table
  base := (16361045993488111067256802643605034062689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1538459062659760100549855015767500000000000)
      linear := (-156042314031101819548547939508009921875000000)
      constant := (4033721809022330250942865040584478405086787588) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509565945183563540977/100000000000000000000)
  centralHi := (254782972591781770489/50000000000000000000)
  directionLo := (512009920572608301107/100000000000000000000)
  directionHi := (128002480143152075277/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree106.table
  base := (6811979392086161860432019383423851237631/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1885094980472225464580501858497031250000000000)
      constant := (49082915226837958622848436865648575595985551185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree106.table
  base := (34059896735623766721820114388953972995461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1890348738869195006160987832455515625000000000)
      constant := (49351518255722537605415379160812315133633502647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (512009920572608301107/100000000000000000000)
  centralHi := (128002480143152075277/25000000000000000000)
  directionLo := (514442285430269465263/100000000000000000000)
  directionHi := (32152642839391841579/6250000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree107.table
  base := (7083950225343442509493148296046841272627/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1902886387209736659351551341630404375000000000)
      constant := (50033921844822122051935977550153217280902836645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree107.table
  base := (17709875466330241327056478675430575958149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-477047427341292044434850097703728046875000000)
      constant := (12576904459502799904933126042734747212715999974) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514442285430269465263/100000000000000000000)
  centralHi := (32152642839391841579/6250000000000000000)
  directionLo := (258431601837250651217/50000000000000000000)
  directionHi := (103372640734900260487/20000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree108.table
  base := (36801654731328436436409198733722832335791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-640225931315749284707533608254592500000000000)
      constant := (16998041222031297289921265271240088598197457519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree108.table
  base := (36801654563829377303665008668096193224433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-642010226620380449772604316391436250000000000)
      constant := (17090986818243838974454300648589590949236190097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258431601837250651217/50000000000000000000)
  centralHi := (103372640734900260487/20000000000000000000)
  directionLo := (129818208850544920963/25000000000000000000)
  directionHi := (519272835402179683853/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree109.table
  base := (38205607761663438783916242876695545223541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1938469200684759048893650307897150625000000000)
      constant := (51963520690297578458573801484668010711665516807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree109.table
  base := (9551401904274752528291239783832904171077/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-971935825178557260448112753766852656250000000)
      constant := (26123773052771939021847673080181444169779059083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129818208850544920963/25000000000000000000)
  centralHi := (519272835402179683853/100000000000000000000)
  directionLo := (52167133701265337213/10000000000000000000)
  directionHi := (521671337012653372131/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree110.table
  base := (39631610207095749898266681856631754979399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1956260607422270243664699791030523750000000000)
      constant := (52942112917133228458377808701929953336865995573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree110.table
  base := (39631610082335436375077387377683324897079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-1961712620853087692474638065893101875000000000)
      constant := (53231374790162232123470234475572481909135473933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52167133701265337213/10000000000000000000)
  centralHi := (521671337012653372131/100000000000000000000)
  directionLo := (262029430663102970953/50000000000000000000)
  directionHi := (524058861326205941907/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree111.table
  base := (10269915514670721166890240385981462300791/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1538459062659760100549855015767500000000000)
      linear := (-164504334513315119869645772846991406250000000)
      constant := (4494158362195701861826852395924143004081111269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree111.table
  base := (41079661951022002655299480925927606181431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-659851197116353621351016874750832812500000000)
      constant := (18074815502782059862067715601276258615604053029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262029430663102970953/50000000000000000000)
  centralHi := (524058861326205941907/100000000000000000000)
  directionLo := (52643555769768224079/10000000000000000000)
  directionHi := (526435557697682240791/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree112.table
  base := (21274881654459016334921282456848143339663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-995921710448646316603399378648635000000000000)
      constant := (27463441488865632685713247513042983792048667501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree112.table
  base := (425497632160200284505966590315891299029/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-499348640461258508907865795652973750000000000)
      constant := (13806690314973554224332320158586139248692289575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52643555769768224079/10000000000000000000)
  centralHi := (526435557697682240791/100000000000000000000)
  directionLo := (528801572125518463167/100000000000000000000)
  directionHi := (8262524564461225987/1562500000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree113.table
  base := (44041913951517889380792019836190379908239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2009634827634803827977848240430643125000000000)
      constant := (55933060811104398710082641787112178832185487253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree113.table
  base := (44041913871364422656548888937699087946807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2015235532341007207209875740971291562500000000)
      constant := (56238319044637967430244171702488866806353427439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528801572125518463167/100000000000000000000)
  centralHi := (8262524564461225987/1562500000000000000)
  directionLo := (265578523678200532229/50000000000000000000)
  directionHi := (531157047356401064459/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree114.table
  base := (2847257123827586397440877836163995967363/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1538459062659760100549855015767500000000000)
      linear := (-168952186197692918562408143630334687500000000)
      constant := (4745702820526656883840711126606554197149548868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree114.table
  base := (45556113912089149663020534506378474424277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-677692167612326792929429433110229375000000000)
      constant := (19086373287479084965926840468999264860779897293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (265578523678200532229/50000000000000000000)
  centralHi := (531157047356401064459/100000000000000000000)
  directionLo := (33343882686610425971/6250000000000000000)
  directionHi := (533502122985766815537/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree115.table
  base := (47092363393734807679177928293053301976353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2045217641109826217519947206697389375000000000)
      constant := (57973002083254825058740472939735676736527141131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree115.table
  base := (588654541675977499344647224032515119323/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-1025458736666476775183350428845042343750000000)
      constant := (29144581856587948349574210505203299584255290965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33343882686610425971/6250000000000000000)
  centralHi := (533502122985766815537/100000000000000000000)
  directionLo := (267918467777172108881/50000000000000000000)
  directionHi := (535836935554344217763/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree116.table
  base := (1216266554634988567105158823957167232959/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-515752261961834353072749172457690625000000000)
      constant := (14751691380451911936575131475110969321409836930) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree116.table
  base := (1946026485357534092447767069342724084209/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2068758443828926721945113416049481250000000000)
      constant := (59328450596758112379563459207600117794686686075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267918467777172108881/50000000000000000000)
  centralHi := (535836935554344217763/100000000000000000000)
  directionLo := (269080809320462603013/50000000000000000000)
  directionHi := (538161618640925206027/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree117.table
  base := (3139438147079941089236705071414559415407/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1538459062659760100549855015767500000000000)
      linear := (-173400037882070717255170514413677968750000000)
      constant := (5004143680157908058164417784853108834232476602) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree117.table
  base := (50231010308890555112320730429893680749911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-695533138108299964507841991469625937500000000)
      constant := (20125660171035152549446374758399975587000131349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269080809320462603013/50000000000000000000)
  centralHi := (538161618640925206027/100000000000000000000)
  directionLo := (540476302951545502743/100000000000000000000)
  directionHi := (67559537868943187843/12500000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree118.table
  base := (12958351973740605677352795890742447646527/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-524647965330589950458273914024377187500000000)
      constant := (15275469500862129653803788252510317470109142629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree118.table
  base := (3239587991042325964070481203673137487681/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-526110096205218266275484633192068593750000000)
      constant := (15358688365538551857489547377800880457556742598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540476302951545502743/100000000000000000000)
  centralHi := (67559537868943187843/12500000000000000000)
  directionLo := (542781116405242097149/100000000000000000000)
  directionHi := (10855622328104841943/2000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree119.table
  base := (6682231851062739889360526419800550085903/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-529095817014967749151036284807720468750000000)
      constant := (15540806761603383805530623726014836897615974212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree119.table
  base := (53457854775483079437732665044509084380407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2122281355316846236680351091127670937500000000)
      constant := (62501769443853122555072649897765741599122154639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542781116405242097149/100000000000000000000)
  centralHi := (10855622328104841943/2000000000000000000)
  directionLo := (136269046054136765707/25000000000000000000)
  directionHi := (545076184216547062829/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree120.table
  base := (13776087773085674746819719303965849261497/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1538459062659760100549855015767500000000000)
      linear := (-177847889566448515947932885197021250000000000)
      constant := (5269480940895504819490245576325451394451425273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree120.table
  base := (55104351063867724403015358639405103760219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-713374108604273136086254549829022500000000000)
      constant := (21192676152720514736933180532551436840029900571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136269046054136765707/25000000000000000000)
  centralHi := (545076184216547062829/100000000000000000000)
  directionLo := (547361628974868247567/100000000000000000000)
  directionHi := (34210101810929265473/6250000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree121.table
  base := (709661209315784379269055856826272327963/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-537991520383723346536561026374407031250000000)
      constant := (16078377684102898179548479510330714719969638270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree121.table
  base := (56772896720707970419202018836280247345419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2157963296308792579837176207846464062500000000)
      constant := (64663530505047768398051496653274214888010548363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547361628974868247567/100000000000000000000)
  centralHi := (34210101810929265473/6250000000000000000)
  directionLo := (54963757072089923211/10000000000000000000)
  directionHi := (549637570720899232111/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree122.table
  base := (58463491766321665721882038756727922900787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2169757488272404580917293588631001250000000000)
      constant := (65402445383383594993802265034848235056283014649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree122.table
  base := (1461587293628719159735055358430974027103/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-543951066701191437853897191551465156250000000)
      constant := (16439568896121914897379147215094939224665520060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54963757072089923211/10000000000000000000)
  centralHi := (549637570720899232111/100000000000000000000)
  directionLo := (551904127020193320233/100000000000000000000)
  directionHi := (275952063510096660117/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree123.table
  base := (60176136154816936144117284048725334886777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-729182965003305258562781023921458125000000000)
      constant := (22166858410547411646536668734382235767746559793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree123.table
  base := (60176136136561314788115088774063872894081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-731215079100246307664667108188419062500000000)
      constant := (22287421232154489572480835182088421596759626879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551904127020193320233/100000000000000000000)
  centralHi := (275952063510096660117/50000000000000000000)
  directionLo := (554161413034029156839/100000000000000000000)
  directionHi := (13854035325850728921/2500000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree124.table
  base := (1934713434695208622240558210003267970913/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-551335075436856742614848138724436875000000000)
      constant := (16901975070293336457015280784249054874182190008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree124.table
  base := (6191082989450737955838591582035813552967/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-1105743103898356047286206941462326875000000000)
      constant := (33987747420481412846324792825457767377829247545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554161413034029156839/100000000000000000000)
  centralHi := (13854035325850728921/2500000000000000000)
  directionLo := (556409541587688841101/100000000000000000000)
  directionHi := (278204770793844420551/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree125.table
  base := (31833786516138921409454564386514668957637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-1111565854242469082615221019015560312500000000)
      constant := (34362210265983763438407454261907923120237532099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree125.table
  base := (509340584149671000212719759259104411003/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2229327178292685266150826441284050312500000000)
      constant := (69097969017977880990828424045701920712207866375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556409541587688841101/100000000000000000000)
  centralHi := (278204770793844420551/50000000000000000000)
  directionLo := (27932431161813153913/5000000000000000000)
  directionHi := (558648623236263078261/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree126.table
  base := (16361591380179788490083304261617689441333/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1538459062659760100549855015767500000000000)
      linear := (-186743592935204113333457626763707812500000000)
      constant := (5820844665334948228608344356975435478625377197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree126.table
  base := (65446365509021964955113073019504832192753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-749056049596219479243079666547815625000000000)
      constant := (23409895409168191515499961775925568104773487977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27932431161813153913/5000000000000000000)
  centralHi := (558648623236263078261/100000000000000000000)
  directionLo := (280439383164045984469/50000000000000000000)
  directionHi := (560878766328091968939/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree127.table
  base := (67247207375498013395077728792837059540103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2258714521959960554772541004297866875000000000)
      constant := (70985046637326852261893224677216084970654112381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree127.table
  base := (33623603682707506502516873142469956879087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-566252279821157902326912889500710859375000000)
      constant := (17842661617385503340181308228256618574913970937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280439383164045984469/50000000000000000000)
  centralHi := (560878766328091968939/100000000000000000000)
  directionLo := (563100077065944443277/100000000000000000000)
  directionHi := (281550038532972221639/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree128.table
  base := (17267524649160216779979226809386979070129/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-569126482174367937385897621857810000000000000)
      constant := (18032288122972673480936283066968086258212531283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree128.table
  base := (69070098587949821726801118739469851081803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2282850089780604780886064116362240000000000000)
      constant := (72520849744091941934095994366744095486486053281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (563100077065944443277/100000000000000000000)
  centralHi := (281550038532972221639/50000000000000000000)
  directionLo := (113062531913206817041/20000000000000000000)
  directionHi := (282656329783017042603/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree129.table
  base := (70915039184256485628129685272618667278389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-764765778478327648104879990188204375000000000)
      constant := (24427484515904657997856546498138974304094237101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree129.table
  base := (221609497427392747213420148673766775873/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3076918125319520201099710031535000000000000)
      linear := (-383448510046096325410746112453606093750000000)
      constant := (12280049341859715324774339580283761347404233495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113062531913206817041/20000000000000000000)
  centralHi := (282656329783017042603/50000000000000000000)
  directionLo := (141879153978741034479/25000000000000000000)
  directionHi := (567516615914964137917/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree130.table
  base := (72782029138521746856109764684151703668587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2312088742172494139085689453697986250000000000)
      constant := (74444949804801685204877331377166130803515705249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree130.table
  base := (14556405826413160342566036931691217947263/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2318532030772551124042889233081033125000000000)
      constant := (74848985390746799598308095744698341461002588505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141879153978741034479/25000000000000000000)
  centralHi := (567516615914964137917/100000000000000000000)
  directionLo := (142428011556172453721/25000000000000000000)
  directionHi := (113942409244937962977/20000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree131.table
  base := (74671068459669554330898269626290777340341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2329880148910005333856738936831359375000000000)
      constant := (75616641263160401725525997727618984391126430407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree131.table
  base := (74671068454105823266072623575577984546461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2336373001268524295621301791440429687500000000)
      constant := (76026917762864680656256495170827357955828110897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (142428011556172453721/25000000000000000000)
  centralHi := (113942409244937962977/20000000000000000000)
  directionLo := (285949524342790821367/50000000000000000000)
  directionHi := (114379809737116328547/20000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree132.table
  base := (76582157147978578353037095116507378991317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-782557185215838842875929473321577500000000000)
      constant := (25599175974265996527363011538811217147679301653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree132.table
  base := (19145539285796007169979463492919104021269/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1538459062659760100549855015767500000000000)
      linear := (-196184497647041455599976195816652187500000000)
      constant := (6434507763960029567558277223540892988407995021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (285949524342790821367/50000000000000000000)
  centralHi := (114379809737116328547/20000000000000000000)
  directionLo := (8969964369026084619/1562500000000000000)
  directionHi := (574077719617669415617/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree133.table
  base := (78515295203764553383802582500265414189489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2365462962385027723398837903098105625000000000)
      constant := (77987609783723361011204889330768541621717331003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree133.table
  base := (19628823799908269299388234779341388320259/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-1186027471130235319389063454079611406250000000)
      constant := (39205255802361606017047015757314020661280729711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8969964369026084619/1562500000000000000)
  centralHi := (574077719617669415617/100000000000000000000)
  directionLo := (288124076760071214607/50000000000000000000)
  directionHi := (115249630704028485843/20000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree134.table
  base := (80470482627372903568164446168030114082817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2383254369122538918169887386231478750000000000)
      constant := (79186886845946266300213621998723317006778175459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree134.table
  base := (3218819304952519827498253627614228332819/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2389895912756443810356539466518619375000000000)
      constant := (79616173074483414804857151205016063322902672825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (288124076760071214607/50000000000000000000)
  centralHi := (115249630704028485843/20000000000000000000)
  directionLo := (72301305389897246401/12500000000000000000)
  directionHi := (578410443119177971209/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree135.table
  base := (82447719419172501467346320563838309243451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-800348591953350037646978956454950625000000000)
      constant := (26798453036492372538300297383249935071593505459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree135.table
  base := (20611929854026313757100524916039435238777/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3076918125319520201099710031535000000000000)
      linear := (-401289480542069496989158670813002656250000000)
      constant := (13471846262801955150247306768035678816688539961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72301305389897246401/12500000000000000000)
  centralHi := (578410443119177971209/100000000000000000000)
  directionLo := (58056467941416655991/10000000000000000000)
  directionHi := (580564679414166559911/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree136.table
  base := (42223502789775196706065634927515539994407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-1209418591298780653855993176249112500000000000)
      constant := (40806513287163420056022856668049771459922126389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree136.table
  base := (42223502788453884900806568987961923974423/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-1212788926874195076756682291618706250000000000)
      constant := (41027612555859696129429139570871032556151038021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58056467941416655991/10000000000000000000)
  centralHi := (580564679414166559911/100000000000000000000)
  directionLo := (116542190344479826189/20000000000000000000)
  directionHi := (291355475861199565473/50000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree137.table
  base := (43234170554453674558230079612850882246333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-1218314294667536251241517917815799062500000000)
      constant := (41419944620253373159181747179661966389300054091) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree137.table
  base := (43234170553315342407210045794822339097803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-610854706061090831272944285399202265625000000)
      constant := (20822153919804494008614247166738901001435944203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116542190344479826189/20000000000000000000)
  centralHi := (291355475861199565473/50000000000000000000)
  directionLo := (73106168465284782659/12500000000000000000)
  directionHi := (584849347722278261273/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree138.table
  base := (17702345201530822781172232202971607618031/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-818139998690861232418028439588323750000000000)
      constant := (28025315702676143447385972980012048147577768395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree138.table
  base := (11063965750711603987304975361559106246789/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1538459062659760100549855015767500000000000)
      linear := (-205104982895028041389182474996350468750000000)
      constant := (7044270773276608716199251482826403878051294152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73106168465284782659/12500000000000000000)
  centralHi := (584849347722278261273/100000000000000000000)
  directionLo := (586979953495112579183/100000000000000000000)
  directionHi := (36686247093444536199/6250000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree139.table
  base := (724617282209666077007712611598086602329/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2472211402810094892025134801898344375000000000)
      constant := (85321200176903678983915579477478072028383210375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree139.table
  base := (90577160274518757446945369422476586519649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2479100765236309668248602258315602187500000000)
      constant := (85783125912035361609703286246832844442162788573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (586979953495112579183/100000000000000000000)
  centralHi := (36686247093444536199/6250000000000000000)
  directionLo := (147275713391387681959/25000000000000000000)
  directionHi := (589102853565550727837/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree140.table
  base := (92664643914991545438141579289649505878099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2490002809547606086796184285031717500000000000)
      constant := (86575648447144397239484542433851765508671100473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree140.table
  base := (3706585756541449428069102067197030669283/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2496941735732282839827014816674998750000000000)
      constant := (87044245577378221863916821822344715594108781025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147275713391387681959/25000000000000000000)
  centralHi := (589102853565550727837/100000000000000000000)
  directionLo := (295609065470354309301/50000000000000000000)
  directionHi := (591218130940708618603/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree141.table
  base := (94774176924427712654438968234371692899433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-835931405428372427189077922721696875000000000)
      constant := (29279763972920848684959970151852607819037640097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree141.table
  base := (94774176923174195229141500317753980208583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-838260902076085337135142458344798437500000000)
      constant := (29438202758453330907891377119310938808669276197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295609065470354309301/50000000000000000000)
  centralHi := (591218130940708618603/100000000000000000000)
  directionLo := (593325867148041219917/100000000000000000000)
  directionHi := (296662933574020609959/50000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree142.table
  base := (3028304978279395275959994379304188868179/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-631396405755657119084570812824615937500000000)
      constant := (22278032647942522626035261181612161598222334064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree142.table
  base := (1938115186077219932914176992405836846957/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-1266311838362114591491919966696895937500000000)
      constant := (44797107002996382762048885512270473609359193475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (593325867148041219917/100000000000000000000)
  centralHi := (296662933574020609959/50000000000000000000)
  directionLo := (59542614227200776901/10000000000000000000)
  directionHi := (595426142272007769011/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree143.table
  base := (309560597052977705617374612861385411213/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-635844257440034917777333183607959218750000000)
      constant := (22598541116544739207177401672750733699813654330) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree143.table
  base := (19811878211204601745687693138964276875951/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2550464647220202354562252491753188437500000000)
      constant := (90883062769288575376656370085779357867766250635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59542614227200776901/10000000000000000000)
  centralHi := (595426142272007769011/100000000000000000000)
  directionLo := (59751903498957705991/10000000000000000000)
  directionHi := (597519034989577059911/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree144.table
  base := (25308768045221061098905398574515731551089/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1538459062659760100549855015767500000000000)
      linear := (-213430703041470905490031851463767500000000000)
      constant := (7640449461833416417089581296237930393164196401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree144.table
  base := (4049402887203337511943545977115559684769/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-856101872572058508713555016704195000000000000)
      constant := (30727051521753122708726695533590864401849788025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59751903498957705991/10000000000000000000)
  centralHi := (597519034989577059911/100000000000000000000)
  directionLo := (14990115565115433603/2500000000000000000)
  directionHi := (599604622604617344121/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree145.table
  base := (12929100334643875699383989627811302915927/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-644739960808790515162857925174645781250000000)
      constant := (23246454454811989925640513399841470195694649108) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree145.table
  base := (103432802676461371891931858096557272259001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2586146588212148697719077608471981562500000000)
      constant := (93488489393916973370654669721080299431183727477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14990115565115433603/2500000000000000000)
  centralHi := (599604622604617344121/100000000000000000000)
  directionLo := (601682981081213373423/100000000000000000000)
  directionHi := (37605186317575835839/6250000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree146.table
  base := (105652582546164873587266475350543298380093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2596751249972673255422481183831956250000000000)
      constant := (94295437297931466659920236222511359472437385111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree146.table
  base := (52826291272785503443909265368816039107253/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-1301993779354060934648745083415689062500000000)
      constant := (47402533627636541308583272144697197684513242931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (601682981081213373423/100000000000000000000)
  centralHi := (37605186317575835839/6250000000000000000)
  directionLo := (301877092537975605487/50000000000000000000)
  directionHi := (24150167403038048439/4000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree147.table
  base := (53947205894166200743479589478766315718189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3076918125319520201099710031535000000000000)
      linear := (-435757109451697408365588444494221562500000000)
      constant := (15935708663010498941986613672116101107365877801) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree147.table
  base := (3371700368369407081367093113895517002099/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3076918125319520201099710031535000000000000)
      linear := (-436971421534015840145983787531795781250000000)
      constant := (16021814691556538630638705861137453844132351231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301877092537975605487/50000000000000000000)
  centralHi := (24150167403038048439/4000000000000000000)
  directionLo := (15145457699230240779/2500000000000000000)
  directionHi := (605818307969209631161/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree148.table
  base := (110158290404054434599167623426749280907403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2632334063447695644964580150098702500000000000)
      constant := (96942261859653855338985122700451173358423264481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree148.table
  base := (110158290403614112991631893365370537317653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2639669499700068212454315283550171250000000000)
      constant := (97465952076126787374108438267008335758427891231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15145457699230240779/2500000000000000000)
  centralHi := (605818307969209631161/100000000000000000000)
  directionLo := (30393771094774760749/5000000000000000000)
  directionHi := (607875421895495214981/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree149.table
  base := (2248884367874513797859272452206990919119/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-1325062735092603419867814816616037812500000000)
      constant := (49139733471357596698501274157689937735794612825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree149.table
  base := (4497768735733862643960333903228176566231/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2657510470196041384032727841909567812500000000)
      constant := (98810259035646935749436926171190854614097717175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30393771094774760749/5000000000000000000)
  centralHi := (607875421895495214981/100000000000000000000)
  directionLo := (304962798886428310349/50000000000000000000)
  directionHi := (609925597772856620699/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree150.table
  base := (7172012234858402092242411783339701841261/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1538459062659760100549855015767500000000000)
      linear := (-222326406410226502875556593030454062500000000)
      constant := (8302155602271497284449104003726271797794573996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree150.table
  base := (5737609787870400823530397589145122312161/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1538459062659760100549855015767500000000000)
      linear := (-222945953391001212967595033355747031250000000)
      constant := (8346984085659222917600319835042488223999832995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304962798886428310349/50000000000000000000)
  centralHi := (609925597772856620699/100000000000000000000)
  directionLo := (24478756213256478571/4000000000000000000)
  directionHi := (152992226332852991069/25000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree151.table
  base := (58541111248231120277572814059737423308477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-1342854141830114614638864299749410937500000000)
      constant := (50490731356646474055759895398793038721361192779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree151.table
  base := (936657779969449721903769272163337577179/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2693192411187987727189552958628360937500000000)
      constant := (101526602052928809075599166183164018491945360375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24478756213256478571/4000000000000000000)
  centralHi := (152992226332852991069/25000000000000000000)
  directionLo := (307002706570510887979/50000000000000000000)
  directionHi := (614005413141021775959/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree152.table
  base := (5971714930514191233609988373648579216213/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-675874922599435106012194520658048750000000000)
      constant := (25586563350207678132632065763961033633930221755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree152.table
  base := (2985857465251047233525268296545289938703/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-677758345420990224691991379246939375000000000)
      constant := (25724659527677985896738957052044039967560195810) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307002706570510887979/50000000000000000000)
  centralHi := (614005413141021775959/100000000000000000000)
  directionLo := (616035188638138604119/100000000000000000000)
  directionHi := (15400879715953465103/2500000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree153.table
  base := (194893478559307079938622229661739189581/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-907097032378417206273275855255189375000000000)
      constant := (34573413096627213614322319791425464816651643125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree153.table
  base := (12180842409935865120041519881389764646709/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1538459062659760100549855015767500000000000)
      linear := (-227406196014994505862198172945596171875000000)
      constant := (8689993100105873614006049932475672093272329640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (616035188638138604119/100000000000000000000)
  centralHi := (15400879715953465103/2500000000000000000)
  directionLo := (618058298151863010847/100000000000000000000)
  directionHi := (19314321817245719089/3125000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree154.table
  base := (62102299482336120931940028891546005099411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-1369541251936381406795438524449470625000000000)
      constant := (52551710190227957270083765932317700199222324297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree154.table
  base := (124204598964492953760230769600768717794867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2746715322675907241924790633706550625000000000)
      constant := (105670439324614631151201071489641717903836335809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (618058298151863010847/100000000000000000000)
  centralHi := (19314321817245719089/3125000000000000000)
  directionLo := (77509350866154305271/12500000000000000000)
  directionHi := (620074806929234442169/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree155.table
  base := (15827852900744176644205855199848113766343/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-689218477652568502090481633008078593750000000)
      constant := (26623949168140878938899275764720388952162783972) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree155.table
  base := (7913926450362442699115372867710209742759/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-1382278146585940206751601596032973593750000000)
      constant := (53535102240377193685965833454450215257694694469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77509350866154305271/12500000000000000000)
  centralHi := (620074806929234442169/100000000000000000000)
  directionLo := (77760597394973031931/12500000000000000000)
  directionHi := (622084779159784255449/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree156.table
  base := (12906309682375702336978198806922700644677/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3076918125319520201099710031535000000000000)
      linear := (-462444219557964200522162669194281250000000000)
      constant := (17982894694369037921838931177672424311203829465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree156.table
  base := (32265774205906045667019923631440001507819/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1538459062659760100549855015767500000000000)
      linear := (-231866438638987798756801312535445312500000000)
      constant := (9039934389141629236759302560961378769108943971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77760597394973031931/12500000000000000000)
  centralHi := (622084779159784255449/100000000000000000000)
  directionLo := (312044138999688522121/50000000000000000000)
  directionHi := (624088277999377044243/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree157.table
  base := (65762709909211320388063573493866604690431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-1396228362042648198952012749149530312500000000)
      constant := (54654067430708817429930221067405135272667108337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree157.table
  base := (65762709909154150889166086150896883797257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-700059558540956689165007077196185078125000000)
      constant := (27474365972864930034498219219106276348793875732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312044138999688522121/50000000000000000000)
  centralHi := (624088277999377044243/100000000000000000000)
  directionLo := (626085365593365313371/100000000000000000000)
  directionHi := (156521341398341328343/25000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree158.table
  base := (134009792190282876874370354728628775376973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2810248130822807592675074981432433750000000000)
      constant := (110728096758183126366935816467946808856628316871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree158.table
  base := (134009792190184466667748544003071565481313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2818079204659799928238440867144136875000000000)
      constant := (111324958146044295591743779345598799682356647051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (626085365593365313371/100000000000000000000)
  centralHi := (156521341398341328343/25000000000000000000)
  directionLo := (628076103099081521391/100000000000000000000)
  directionHi := (39254756443692595087/6250000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree159.table
  base := (136516213939663464250082403250509638385591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-942679845853439595815374821521935625000000000)
      constant := (37385751285506632168650872270019816076241900719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree159.table
  base := (136516213939578767126390520675965706670247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-945306725051924366605617808501177812500000000)
      constant := (37587231811154160579622803352254526399978322773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (628076103099081521391/100000000000000000000)
  centralHi := (39254756443692595087/6250000000000000000)
  directionLo := (78757568838461315137/12500000000000000000)
  directionHi := (630060550707690521097/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree160.table
  base := (17380585633360418647708894048348033762451/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-711457736074457495554293486924795000000000000)
      constant := (28398901539109237043377865455166452398025408754) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree160.table
  base := (139044685066810457134735764594455299066753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2853761145651746271395265983862930000000000000)
      constant := (114207675753723290161473711982927052226757236931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78757568838461315137/12500000000000000000)
  centralHi := (630060550707690521097/100000000000000000000)
  directionLo := (632038767665424488659/100000000000000000000)
  directionHi := (31601938383271224433/5000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree161.table
  base := (141595205572254795994945675952620939569117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2863622351035341176988223430832553125000000000)
      constant := (115043153657943095654736964226346647677233090559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree161.table
  base := (141595205572192066065002534817092190535569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2871602116147719442973678542222326562500000000)
      constant := (115662899106835542626149289922534961772501412413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (632038767665424488659/100000000000000000000)
  centralHi := (31601938383271224433/5000000000000000000)
  directionLo := (634010812294221535901/100000000000000000000)
  directionHi := (317005406147110767951/50000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree162.table
  base := (72083887728041750308654422661958607471387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (3076918125319520201099710031535000000000000)
      linear := (-480235626295475395293212152327654375000000000)
      constant := (19416649393507827971428654146238237190042030283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree162.table
  base := (144167775456029518137138114346440807781489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-963147695547897538184030366860574375000000000)
      constant := (39042455164269291485283865277633564636587905001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (634010812294221535901/100000000000000000000)
  centralHi := (317005406147110767951/50000000000000000000)
  directionLo := (1242142074241774113/195312500000000000)
  directionHi := (635976742011788345857/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree163.table
  base := (146762394718668711187179361446421971989947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2899205164510363566530322397099299375000000000)
      constant := (117965834265757011572219488445509789497500858969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree163.table
  base := (146762394718622258115187774903609172163111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2907284057139665786130503658941119687500000000)
      constant := (118601074911648738077935335598895964757433290447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1242142074241774113/195312500000000000)
  centralHi := (635976742011788345857/100000000000000000000)
  directionLo := (637936613351106356851/100000000000000000000)
  directionHi := (159484153337776589213/25000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree164.table
  base := (3734476584007583847906238389029454866049/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-729249142811968690325342970058168125000000000)
      constant := (29860241843020373828464273449997166764102151230) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree164.table
  base := (2987581267205267631077923776858108374317/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-1462562513817819478854458108650258125000000000)
      constant := (60042013681683203350312143543532915021577398975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (637936613351106356851/100000000000000000000)
  centralHi := (159484153337776589213/25000000000000000000)
  directionLo := (319945240989700121463/50000000000000000000)
  directionHi := (639890481979400242927/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree165.table
  base := (9501111336329635168331563804158855333889/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (1538459062659760100549855015767500000000000)
      linear := (-244565664832115496339368446947170468750000000)
      constant := (10077107973335709390913624464474670421045465154) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree165.table
  base := (152017781381239768181090307267048749247797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-980988666043870709762442925219970937500000000)
      constant := (40525407615989659359331940548728914892121740723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319945240989700121463/50000000000000000000)
  centralHi := (639890481979400242927/100000000000000000000)
  directionLo := (641838402716586696417/100000000000000000000)
  directionHi := (320919201358293348209/50000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree166.table
  base := (154678548781861811165997990513683799432777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2952579384722897150843470846499418750000000000)
      constant := (122418819189605986278590965658170037333151496379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree166.table
  base := (77339274390916108617874225078603058425091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141135000000000000000000000000000000000000000
      center := (2371068)
      previous := (1185534)
      next := (1185534)
      square := (9230754375958560603299130094605000000000000)
      linear := (-1480403484313792650432870667009654687500000000)
      constant := (61538830682732189165084290157183554120985356157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (641838402716586696417/100000000000000000000)
  centralHi := (320919201358293348209/50000000000000000000)
  directionLo := (10059069211769075161/1562500000000000000)
  directionHi := (128756085910644162061/20000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree167.table
  base := (157361365562341046247527619958692162408537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 282270000000000000000000000000000000000000000
      center := (4742136)
      previous := (2371068)
      next := (2371068)
      square := (18461508751917121206598260189210000000000000)
      linear := (-2970370791460408345614520329632791875000000000)
      constant := (123921537900821671357858383179009629303071398899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree167.table
  base := (15736136556231558378073771473751185937991/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-744661984780889618111038473094676484375000000)
      constant := (31147085728965091447750528161238140173664531455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10059069211769075161/1562500000000000000)
  centralHi := (128756085910644162061/20000000000000000000)
  directionLo := (322858307833978340779/50000000000000000000)
  directionHi := (645716615667956681559/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree168.table
  base := (160066231722980822174070855696421465618283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-996054066065973180128523270922055000000000000)
      constant := (41811150604561053233330104268308361445002424747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree168.table
  base := (160066231722958915178181128120266654593881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (1580712)
      previous := (790356)
      next := (790356)
      square := (6153836250639040402199420063070000000000000)
      linear := (-998829636539843881340855483579367500000000000)
      constant := (42036089166388178286795688441414004421823826329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell044.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322858307833978340779/50000000000000000000)
  centralHi := (645716615667956681559/100000000000000000000)
  directionLo := (64764701344453821077/10000000000000000000)
  directionHi := (647647013444538210771/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree169.table
  base := (2543642926000694287354107723607874606669/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-751488401233857683789154823974884531250000000)
      constant := (31738640232049470836378440757473470298675540058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 8999
  qDenominator := 18624
  table := BinomialMassData.Q8999_18624.Degree169.table
  base := (81396573632012793529361203309832836099989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70567500000000000000000000000000000000000000
      center := (1185534)
      previous := (592767)
      next := (592767)
      square := (4615377187979280301649565047302500000000000)
      linear := (-753582470028876203900244752274374765625000000)
      constant := (31909358778846079960562404633159063252438796314) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8999_18624.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell044.Kernel169
