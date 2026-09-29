import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell071.Parameters
import ForestUnimodality.BinomialMassData.Q10429_20604.Batch000_049
import ForestUnimodality.BinomialMassData.Q10429_20604.Batch050_099
import ForestUnimodality.BinomialMassData.Q10429_20604.Batch100_149
import ForestUnimodality.BinomialMassData.Q5227_10302.Batch000_049
import ForestUnimodality.BinomialMassData.Q5227_10302.Batch050_099
import ForestUnimodality.BinomialMassData.Q5227_10302.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree000.table
  base := (314621658668488820237385537/5000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (126)
      previous := (63)
      next := (63)
      square := (772293669894491136007630420000000000000)
      linear := (-15511006872523944513653227000000000000)
      constant := (629243317336977640474771074000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree000.table
  base := (314621658668488820237385537/5000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (126)
      previous := (63)
      next := (63)
      square := (772293669894491136007630420000000000000)
      linear := (-15511006872523944513653227000000000000)
      constant := (629243317336977640474771074000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree001.table
  base := (178287069575045540703985608178627766734607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-21155273093573818759410227093037417000000000000)
      constant := (9466368849054518467964799931501383135187494688414) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree001.table
  base := (355922632266094504477832128006377063269253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-21204999152244150307429918396705167000000000000)
      constant := (9449108245609891595317706733367903335187499267653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (3124659836470982793/6250000000000000000)
  directionHi := (49994557383535724689/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree002.table
  base := (210975252414800614995984906513913525924241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-41898995728489327331304651331076007000000000000)
      constant := (5619180457271415130999541803284241536056227529041) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree002.table
  base := (210282074441307416125018357303976032729497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-41998447845829990427344033938411507000000000000)
      constant := (5600890301562519356753196844200296644181230731097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3124659836470982793/6250000000000000000)
  centralHi := (49994557383535724689/100000000000000000000)
  directionLo := (70702981096636179193/100000000000000000000)
  directionHi := (35351490548318089597/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree003.table
  base := (32931730492716065512597165671462527810751/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-6960302040378315100355452841012733000000000000)
      constant := (393661988261462679957587810715729522604276419356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree003.table
  base := (1024720266726321255642353997929210708229/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-6976877393268425616362016608901983000000000000)
      constant := (392028382689754328830891264337621186554351920768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70702981096636179193/100000000000000000000)
  centralHi := (35351490548318089597/50000000000000000000)
  directionLo := (17318622698040325791/20000000000000000000)
  directionHi := (21648278372550407239/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree004.table
  base := (87341251998124709861613358791165205227281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-83386440998320344475093499807153187000000000000)
      constant := (2402239086594799667003276992898391001419606544081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree004.table
  base := (86924686674043819041290713005451751861899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-83585345233001670667172265021824187000000000000)
      constant := (2391591634395081058695715405818395725253145649099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17318622698040325791/20000000000000000000)
  centralHi := (21648278372550407239/25000000000000000000)
  directionLo := (99989114767071449377/100000000000000000000)
  directionHi := (49994557383535724689/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree005.table
  base := (61463357747554779736572930361052572419937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-104130163633235853046987924045191777000000000000)
      constant := (1763083131572448697299409268230710877056276853537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree005.table
  base := (61163664966765313025743489584074658155287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-104378793926587510787086380563530527000000000000)
      constant := (1755763931973684800847026827727256496477257068887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99989114767071449377/100000000000000000000)
  centralHi := (49994557383535724689/50000000000000000000)
  directionLo := (27947807203649976417/25000000000000000000)
  directionHi := (111791228814599905669/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree006.table
  base := (45553988434260297940049156911227333635593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-13874876252016817957653594253692263000000000000)
      constant := (155435531946824476970079487417207889290421731777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree006.table
  base := (45336979398822620605940540415738933681397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-13908026957797038989666721789470763000000000000)
      constant := (154896901705962593395961470516904850257856000333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27947807203649976417/25000000000000000000)
  centralHi := (111791228814599905669/100000000000000000000)
  directionLo := (122461155505955759687/100000000000000000000)
  directionHi := (15307644438244469961/12500000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree007.table
  base := (35142193642504201676159313641840894817259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-145617608903066870190776772521268957000000000000)
      constant := (1191122216780095697809535392018723804848264412459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree007.table
  base := (34980526784834983602677367565907459310833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-145965691313759191026914611646943207000000000000)
      constant := (1188071023073842911847639344591072783809929133233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122461155505955759687/100000000000000000000)
  centralHi := (15307644438244469961/12500000000000000000)
  directionLo := (132273165743583551393/100000000000000000000)
  directionHi := (66136582871791775697/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree008.table
  base := (13932772480888721745044000435793847371049/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-166361331537982378762671196759307547000000000000)
      constant := (1077008576455692047717695792542725404640832556498) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree008.table
  base := (27740187286460774295632867967883206157573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-166759140007345031146828727188649547000000000000)
      constant := (1075299261933352936379621673774881896220859051973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132273165743583551393/100000000000000000000)
  centralHi := (66136582871791775697/50000000000000000000)
  directionLo := (70702981096636179193/50000000000000000000)
  directionHi := (141405962193272358387/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree009.table
  base := (22459472354151306206066047540063773461811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-20789450463655320814951735666371793000000000000)
      constant := (113669586820142693049470127849579839341256929179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree009.table
  base := (22358094216060157058821755764638286792307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-20839176522325652362971426970039543000000000000)
      constant := (113598011713835166202513578181215066771245551323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70702981096636179193/50000000000000000000)
  centralHi := (141405962193272358387/100000000000000000000)
  directionLo := (74991836075303587033/50000000000000000000)
  directionHi := (149983672150607174067/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree010.table
  base := (9116886863541356078324080453750069694349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-207848776807813395906460045235384727000000000000)
      constant := (1010862336785643203314271335678167813372585683098) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree010.table
  base := (18148714863417210949187297930336852236877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-208346037394516711386656958272062227000000000000)
      constant := (1011130450568183892762784305074603458367462302477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74991836075303587033/50000000000000000000)
  centralHi := (149983672150607174067/100000000000000000000)
  directionLo := (15809667194396112417/10000000000000000000)
  directionHi := (158096671943961124171/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree011.table
  base := (14800850520826780615031098158799961750061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-228592499442728904478354469473423317000000000000)
      constant := (1030232667215171414231810539870929175921980250861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree011.table
  base := (7363729008098135813309866203074454914317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-229139486088102551506571073813768567000000000000)
      constant := (1031340015261104200061179343241598980350090023834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15809667194396112417/10000000000000000000)
  centralHi := (158096671943961124171/100000000000000000000)
  directionLo := (165813188401080180503/100000000000000000000)
  directionHi := (20726648550135022563/12500000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree012.table
  base := (2983574209494793631093287120485488968603/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-27704024675293823672249877079051323000000000000)
      constant := (119458898894312575392415773527732609751839398668) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree012.table
  base := (5934879622874798800381562178008249663129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-27770326086854265736276132150608323000000000000)
      constant := (119672497356254243739416653328647631482248620962) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165813188401080180503/100000000000000000000)
  centralHi := (20726648550135022563/12500000000000000000)
  directionLo := (173186226980403257911/100000000000000000000)
  directionHi := (21648278372550407239/12500000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree013.table
  base := (1899007761164044753930969419541589206183/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-270079944712559921622143317949500497000000000000)
      constant := (1141864585897398160266607031200655956657007542915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree013.table
  base := (2359407921222355274083921623503417108403/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-270726383475274231746399304897181247000000000000)
      constant := (1144606655316029401527731534241489174329008907212) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173186226980403257911/100000000000000000000)
  centralHi := (21648278372550407239/12500000000000000000)
  directionLo := (180257940140464835499/100000000000000000000)
  directionHi := (360515880280929671/200000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree014.table
  base := (1478504675526397409810825910528082185391/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-290823667347475430194037742187539087000000000000)
      constant := (1228033528792415519745479974671354408183122550955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree014.table
  base := (7341145957438039710378757149577652540761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-291519832168860071866313420438887587000000000000)
      constant := (1231616474348150705185200324761211061911156001561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180257940140464835499/100000000000000000000)
  centralHi := (360515880280929671/200000000000000000)
  directionLo := (187062504932600136089/100000000000000000000)
  directionHi := (18706250493260013609/10000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree015.table
  base := (1391032524973681813667918670874621014791/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-34618598886932326529548018491730853000000000000)
      constant := (147997269189121813634683619522481157371496737596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree015.table
  base := (172438491443426359008741228335962221353/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-34701475651382879109580837331177103000000000000)
      constant := (148492191870818605895288961349263990433963021344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187062504932600136089/100000000000000000000)
  centralHi := (18706250493260013609/10000000000000000000)
  directionLo := (193628088147444911683/100000000000000000000)
  directionHi := (48407022036861227921/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree016.table
  base := (991022033185842948737564060827115841873/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-332311112617306447337826590663616267000000000000)
      constant := (1452475839040697731244282670170653892145455105092) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree016.table
  base := (980678033697505657967792543668076827897/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-333106729556031752106141651522300267000000000000)
      constant := (1457837131123827811057906653451230122109209397988) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193628088147444911683/100000000000000000000)
  centralHi := (48407022036861227921/25000000000000000000)
  directionLo := (99989114767071449377/50000000000000000000)
  directionHi := (39995645906828579751/20000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree017.table
  base := (2557376878475782153964003587134818852029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 918090000000000000000000000000000000000000000
      center := (11567934)
      previous := (5783967)
      next := (5783967)
      square := (70903509539343336705724541229780000000000000)
      linear := (-1221643028554401231521526003119913000000000000)
      constant := (5496905132382310888665653292396224083985930461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree017.table
  base := (2520274345188843495043810674376659375679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 918090000000000000000000000000000000000000000
      center := (11567934)
      previous := (5783967)
      next := (5783967)
      square := (70903509539343336705724541229780000000000000)
      linear := (-1224568090829126616699154903335663000000000000)
      constant := (5518727860979920583288221010287535220621713311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99989114767071449377/50000000000000000000)
  centralHi := (39995645906828579751/20000000000000000000)
  directionLo := (103066420399160547327/50000000000000000000)
  directionHi := (41226568159664218931/20000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree018.table
  base := (32906521378695544926511934716746027287/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-41533173098570829386846159904410383000000000000)
      constant := (193292083925822644629073688098710944653540181720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree018.table
  base := (1283044704695080447958300968104518060367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-41632625215911492482885542511745883000000000000)
      constant := (194102347712853452008037937980259779544069288663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103066420399160547327/50000000000000000000)
  centralHi := (41226568159664218931/20000000000000000000)
  directionLo := (212108943289908537579/100000000000000000000)
  directionHi := (10605447164495426879/5000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree019.table
  base := (218234747025465882915887487557365454839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-394542280522052973053509863377732037000000000000)
      constant := (1904948226198632545712250143437834911697517674039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree019.table
  base := (94278151641455834562691004985812045843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-395487075636789272465883998147419287000000000000)
      constant := (1913267353848479834313011329097054213171510392486) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212108943289908537579/100000000000000000000)
  centralHi := (10605447164495426879/5000000000000000000)
  directionLo := (217921223361877450881/100000000000000000000)
  directionHi := (108960611680938725441/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree020.table
  base := (-37763097160019962169200746324715529883/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-415286003156968481625404287615770627000000000000)
      constant := (2084071533875610330883912217402861494280096154340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree020.table
  base := (-781724234302308938055678240909279716891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-416280524330375112585798113689125627000000000000)
      constant := (2093459282764103498085771534102060812218394758309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217921223361877450881/100000000000000000000)
  centralHi := (108960611680938725441/50000000000000000000)
  directionLo := (223582457629199811337/100000000000000000000)
  directionHi := (111791228814599905669/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree021.table
  base := (-809849102992033001012940044770979070117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-48447747310209332244144301317089913000000000000)
      constant := (252954249190882501866225404579286768668315687174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree021.table
  base := (-164324379917006365379586233928709044329/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-48563774780440105856190247692314663000000000000)
      constant := (254120785208297277426306424299748191322131627190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223582457629199811337/100000000000000000000)
  centralHi := (111791228814599905669/50000000000000000000)
  directionLo := (114551921772932922899/50000000000000000000)
  directionHi := (229103843545865845799/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree022.table
  base := (-1194026319986117915506931089839354184329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-456773448426799498769193136091847807000000000000)
      constant := (2482153994150477304887621354889329573417362648942) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree022.table
  base := (-1204480445881479775242482658779647681823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-457867421717546792825626344772538307000000000000)
      constant := (2493806880866693725193059156858681859416158047554) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114551921772932922899/50000000000000000000)
  centralHi := (229103843545865845799/100000000000000000000)
  directionLo := (1831994217633849737/781250000000000000)
  directionHi := (234495259857132766337/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree023.table
  base := (-1535629900293507128845472540881510556327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-477517171061715007341087560329886397000000000000)
      constant := (2700478663790176498200698908266951032659152836146) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree023.table
  base := (-308979067292632581899186307654827551177/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-478660870411132632945540460314244647000000000000)
      constant := (2713329114949566071953860647214689252453033432230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1831994217633849737/781250000000000000)
  centralHi := (234495259857132766337/100000000000000000000)
  directionLo := (119882737147013652363/50000000000000000000)
  directionHi := (239765474294027304727/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree024.table
  base := (-3678555897288778325420738301720372944537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-55362321521847835101442442729769443000000000000)
      constant := (325701909903270399473191808853779589446312860207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree024.table
  base := (-461868779751676220699764906033134284499/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-55494924344968719229494952872883443000000000000)
      constant := (327267690418498533515311945772085517442765020712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119882737147013652363/50000000000000000000)
  centralHi := (239765474294027304727/100000000000000000000)
  directionLo := (122461155505955759687/50000000000000000000)
  directionHi := (391875697619058431/160000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree025.table
  base := (-4217754973778150122476702401289086556149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-519004616331546024484876408805963577000000000000)
      constant := (3174462241701734686617339306474574260433923256651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree025.table
  base := (-4232234784066558756501194006559987318299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-520247767798304313185368691397657327000000000000)
      constant := (3189840348905575523004708413562727774421048974501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122461155505955759687/50000000000000000000)
  centralHi := (391875697619058431/160000000000000000)
  directionLo := (249972786917678623443/100000000000000000000)
  directionHi := (62493196729419655861/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree026.table
  base := (-2347737167279265837171847415114132359933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-539748338966461533056770833044002167000000000000)
      constant := (3429738245883534602511351337410799127112474675334) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree026.table
  base := (-4708243188101845193946966394907913520697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-541041216491890153305282806939363667000000000000)
      constant := (3446447433676141313204181490325973764230137117703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249972786917678623443/100000000000000000000)
  centralHi := (62493196729419655861/25000000000000000000)
  directionLo := (254923223672082900321/100000000000000000000)
  directionHi := (127461611836041450161/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree027.table
  base := (-5117321174830649542751996929611960678951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-62276895733486337958740584142448973000000000000)
      constant := (410777380786711590002550955777328880453952025361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree027.table
  base := (-5128564829798724633652289343011906253257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-62426073909497332602799658053452223000000000000)
      constant := (412786907353270637132005230123158835805741824127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254923223672082900321/100000000000000000000)
  centralHi := (127461611836041450161/50000000000000000000)
  directionLo := (259779340470604886867/100000000000000000000)
  directionHi := (64944835117651221717/25000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree028.table
  base := (-2744024252992035292728687609372503148763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-581235784236292550200559681520079347000000000000)
      constant := (3976110674586993698239132040570878889163995849674) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree028.table
  base := (-2748967846669774284697782986824363567781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-582628113879061833545111038022776347000000000000)
      constant := (3995618887489609306059830047755680665008833430838) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259779340470604886867/100000000000000000000)
  centralHi := (64944835117651221717/25000000000000000000)
  directionLo := (264546331487167102787/100000000000000000000)
  directionHi := (66136582871791775697/25000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree029.table
  base := (-1162337235812770583630040497431931746651/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-601979506871208058772454105758117937000000000000)
      constant := (4266974065167464598142824014295081760102633002745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree029.table
  base := (-2910184764064333810051586073422963181491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-603421562572647673665025153564482687000000000000)
      constant := (4287951101592452525313330055922412348650344827418) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264546331487167102787/100000000000000000000)
  centralHi := (66136582871791775697/25000000000000000000)
  directionLo := (269228930970083055329/100000000000000000000)
  directionHi := (26922893097008305533/10000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree030.table
  base := (-1522912844497137430338852534992750547677/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-69191469945124840816038725555128503000000000000)
      constant := (507721770151213959776361049184222180622597842988) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree030.table
  base := (-1524817108773478600621553360650181886183/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-69357223474025945976104363234021003000000000000)
      constant := (510220949024562810418671339640507628733378582852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269228930970083055329/100000000000000000000)
  centralHi := (26922893097008305533/10000000000000000000)
  directionLo := (273831468314489730747/100000000000000000000)
  directionHi := (68457867078622432687/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree031.table
  base := (-6330842005840863126182548391688297498347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-643466952141039075916242954234195117000000000000)
      constant := (4883599383681566195585402720618550955447561220053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree031.table
  base := (-6337516305024582696870896102277751978367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-645008459959819353904853384647895367000000000000)
      constant := (4907654688675029546620033104995064129530632084033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273831468314489730747/100000000000000000000)
  centralHi := (68457867078622432687/25000000000000000000)
  directionLo := (27835791493551075209/10000000000000000000)
  directionHi := (278357914935510752091/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree032.table
  base := (-6531715720312730582767233712756223956411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-664210674775954584488137378472233707000000000000)
      constant := (5209219213586919975268388113354104692253114262789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree032.table
  base := (-6537557871429886845108854253106920284929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-665801908653405194024767500189601707000000000000)
      constant := (5234884678326647268070607820791298596357115543871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27835791493551075209/10000000000000000000)
  centralHi := (278357914935510752091/100000000000000000000)
  directionLo := (70702981096636179193/25000000000000000000)
  directionHi := (282811924386544716773/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree033.table
  base := (-3348178439761171537187347894779209334629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-76106044156763343673336866967808033000000000000)
      constant := (616255568579758253466359439041839042563765852038) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree033.table
  base := (-3350732823155021014546680866065882275413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-76288373038554559349409068414589783000000000000)
      constant := (619291502291938515193490351799609954877119928486) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70702981096636179193/25000000000000000000)
  centralHi := (282811924386544716773/100000000000000000000)
  directionLo := (143598433437830662081/50000000000000000000)
  directionHi := (287196866875661324163/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree034.table
  base := (-6826533276504688918599647803316182619899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 918090000000000000000000000000000000000000000
      center := (11567934)
      previous := (5783967)
      next := (5783967)
      square := (70903509539343336705724541229780000000000000)
      linear := (-2441862007078842912221198017122183000000000000)
      constant := (20397215190565649073715840523171174089849692709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree034.table
  base := (-6830996623910558497446156443287431001071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 918090000000000000000000000000000000000000000
      center := (11567934)
      previous := (5783967)
      next := (5783967)
      square := (70903509539343336705724541229780000000000000)
      linear := (-2447712131628293682576455817553683000000000000)
      constant := (20497662967469734892949162785921691247222672561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143598433437830662081/50000000000000000000)
  centralHi := (287196866875661324163/100000000000000000000)
  directionLo := (291515859107479741187/100000000000000000000)
  directionHi := (72878964776869935297/25000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree035.table
  base := (-6923744234970553631353123170757855867069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-726441842680701110203820651186349477000000000000)
      constant := (6254664650896212024940967209463455361092375769731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree035.table
  base := (-3463820165467768977769599255202968823139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-728182254734162714384509846814720727000000000000)
      constant := (6285448387924943393600897608650365834712897435322) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291515859107479741187/100000000000000000000)
  centralHi := (72878964776869935297/25000000000000000000)
  directionLo := (59154358040349867569/20000000000000000000)
  directionHi := (147885895100874668923/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree036.table
  base := (-139785227790375357566445892354847828623/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-83020618368401846530635008380487563000000000000)
      constant := (736208306628698568913680840443296263988132427650) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree036.table
  base := (-6992659551268620931301865775706572763557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-83219522603083172722713773595158563000000000000)
      constant := (739829042934725113786010748045785223608058007427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59154358040349867569/20000000000000000000)
  centralHi := (147885895100874668923/50000000000000000000)
  directionLo := (74991836075303587033/25000000000000000000)
  directionHi := (299967344301214348133/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree037.table
  base := (-7024163267064692733792760291107017485217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-767929287950532127347609499662426657000000000000)
      constant := (7008396900019679448923192981979101401861216897183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree037.table
  base := (-439195302865726412929088977141462493629/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-769769152121334394624338077898133407000000000000)
      constant := (7042835188081073720675637795810785795421247602736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74991836075303587033/25000000000000000000)
  centralHi := (299967344301214348133/100000000000000000000)
  directionLo := (304105020371415306407/100000000000000000000)
  directionHi := (38013127546426913301/12500000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree038.table
  base := (-3514682306910574561205324356374430076913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-788673010585447635919503923900465247000000000000)
      constant := (7402206801201158729798891739939839849061705353374) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree038.table
  base := (-3515971907539524110728767023431466402741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-790562600814920234744252193439839747000000000000)
      constant := (7438545711749931554399635850345703810595774384918) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304105020371415306407/100000000000000000000)
  centralHi := (38013127546426913301/12500000000000000000)
  directionLo := (308187149607303654283/100000000000000000000)
  directionHi := (77046787401825913571/25000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree039.table
  base := (-7005641267296854941597645876322538518493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-89935192580040349387933149793167093000000000000)
      constant := (867475986451166423901421758924195160741554490123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree039.table
  base := (-7007885905463911910921805034231445590431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-90150672167611786096018478775727343000000000000)
      constant := (871730282427543286363285053031209661300751863641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308187149607303654283/100000000000000000000)
  centralHi := (77046787401825913571/25000000000000000000)
  directionLo := (156107955395497230403/50000000000000000000)
  directionHi := (312215910790994460807/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree040.table
  base := (-695365125061593765432111349807093039957/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-830160455855278653063292772376542427000000000000)
      constant := (8223610671401090832591357375200760449823358704430) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree040.table
  base := (-1738900859892034850642970678072167479197/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-832149498202091914984080424523252427000000000000)
      constant := (8263898370430224403785833439638214046543177436812) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156107955395497230403/50000000000000000000)
  centralHi := (312215910790994460807/100000000000000000000)
  directionLo := (316193343887922248341/100000000000000000000)
  directionHi := (158096671943961124171/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree041.table
  base := (-3436976331609505301882282441583937802513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-850904178490194161635187196614581017000000000000)
      constant := (8651172373281541777081943509581822096479090542174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree041.table
  base := (-687564944446505636271270074137555122069/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-852942946895677755103994540064958767000000000000)
      constant := (8693508524139651871636178527289657197696125147310) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316193343887922248341/100000000000000000000)
  centralHi := (158096671943961124171/50000000000000000000)
  directionLo := (80030340530561245501/25000000000000000000)
  directionHi := (64024272424448996401/20000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree042.table
  base := (-6767018854631314090951723743030020244523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-96849766791678852245231291205846623000000000000)
      constant := (1009995158268121555911145741771882454147344433453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree042.table
  base := (-3384246383122564002917022859163175305967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-97081821732140399469323183956296123000000000000)
      constant := (1014932284797350448809680101769882858350814105874) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80030340530561245501/25000000000000000000)
  centralHi := (64024272424448996401/20000000000000000000)
  directionLo := (40500220341795894731/12500000000000000000)
  directionHi := (324001762734367157849/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree043.table
  base := (-6633251293974985430195373266121483153813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-892391623760025178778976045090658197000000000000)
      constant := (9539952172695422196891126346200456461655027279787) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree043.table
  base := (-829316360471367865995667815129212450483/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-894529844282849435343822771148371447000000000000)
      constant := (9586533941312168137175342485126505137616897656936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40500220341795894731/12500000000000000000)
  centralHi := (324001762734367157849/100000000000000000000)
  directionLo := (327836236592224193347/100000000000000000000)
  directionHi := (81959059148056048337/25000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree044.table
  base := (-1618247621295823544947979862981416575511/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-913135346394940687350870469328696787000000000000)
      constant := (10001150583605425199684751080942866012215460654756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree044.table
  base := (-1294820154388150819441435786716385548537/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-915323292976435275463736886690077787000000000000)
      constant := (10049929717659776824050570991224194952006959689315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327836236592224193347/100000000000000000000)
  centralHi := (81959059148056048337/25000000000000000000)
  directionLo := (331626376802160361007/100000000000000000000)
  directionHi := (20726648550135022563/6250000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree045.table
  base := (-1257305044941146534259515889761499122149/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-103764341003317355102529432618526153000000000000)
      constant := (1163727110507153236110775416695979631572414383695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree045.table
  base := (-6287488111379424417401696797252325359401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-104012971296669012842627889136864903000000000000)
      constant := (1169396701367979006314764527703725011883528865311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331626376802160361007/100000000000000000000)
  centralHi := (20726648550135022563/6250000000000000000)
  directionLo := (167686843221899858503/50000000000000000000)
  directionHi := (335373686443799717007/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree046.table
  base := (-6074100453411215262414697596158152649647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-954622791664771704494659317804773967000000000000)
      constant := (10957125906604952301088850234572765795719293428753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree046.table
  base := (-759366887033389188415915931871861367553/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-956910190363606955703565117773490467000000000000)
      constant := (11010449299178285302208987777540371195681027152376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167686843221899858503/50000000000000000000)
  centralHi := (335373686443799717007/100000000000000000000)
  directionLo := (169539792767715550637/50000000000000000000)
  directionHi := (13563183421417244051/4000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree047.table
  base := (-2917961958083827095136580110501341998439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-975366514299687213066553742042812557000000000000)
      constant := (11451890807673905641287133448802136864044951404722) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree047.table
  base := (-364790440855966679092489727761976157807/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-977703639057192795823479233315196807000000000000)
      constant := (11507561230356337021404758150723367541310596361488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169539792767715550637/50000000000000000000)
  centralHi := (13563183421417244051/4000000000000000000)
  directionLo := (342745417321450678743/100000000000000000000)
  directionHi := (42843177165181334843/12500000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree048.table
  base := (-5572171810155860390627395372354406631309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-110678915214955857959827574031205683000000000000)
      constant := (1328648224751833769779425818739849033708710881499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree048.table
  base := (-5572798055456781431949921631276676047433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-110944120861197626215932594317433683000000000000)
      constant := (1335100165248193498486206266307129039387999294463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342745417321450678743/100000000000000000000)
  centralHi := (42843177165181334843/12500000000000000000)
  directionLo := (346372453960806515823/100000000000000000000)
  directionHi := (21648278372550407239/6250000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree049.table
  base := (-5282993575480259151903929267432446292681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1016853959569518230210342590518889737000000000000)
      constant := (12474951586818195025874758370899521277073107270519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree049.table
  base := (-2641767837816803946404599352135328916109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1019290536444364476063307464398609487000000000000)
      constant := (12535466154256733622196330928542215866098668417382) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346372453960806515823/100000000000000000000)
  centralHi := (21648278372550407239/6250000000000000000)
  directionLo := (349961901684750072821/100000000000000000000)
  directionHi := (174980950842375036411/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree050.table
  base := (-4968515958319567523728585290407847617011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1037597682204433738782237014756928327000000000000)
      constant := (13003240136897841524953882359211419907839522922189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree050.table
  base := (-155280782000336591835802154043477575349/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1040083985137950316183221579940315827000000000000)
      constant := (13066251911912289522528270434146987527649679278432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349961901684750072821/100000000000000000000)
  centralHi := (174980950842375036411/50000000000000000000)
  directionLo := (70702981096636179193/20000000000000000000)
  directionHi := (176757452741590447983/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree051.table
  base := (-2314423228541372783775907090544038725233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7878167726593704078413837914420000000000000)
      linear := (-406897887289253843657874447902717000000000000)
      constant := (5206726959158612330382465110632342521927796334) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree051.table
  base := (-1157313041385062155397115070508677888859/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7878167726593704078413837914420000000000000)
      linear := (-407872908047495638717084081307967000000000000)
      constant := (5231932312956611026207660505576223407422997364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70702981096636179193/20000000000000000000)
  centralHi := (176757452741590447983/50000000000000000000)
  directionLo := (357032553371198868821/100000000000000000000)
  directionHi := (178516276685599434411/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree052.table
  base := (-2132038122630595997697561577690800992573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1079085127474264755926025863233005507000000000000)
      constant := (14093319219351218707749763592849666884466916226054) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree052.table
  base := (-4264427019310571556190962896592216276853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1081670882525121996423049811023728507000000000000)
      constant := (14161475870715018807923581906501357681377298444747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (357032553371198868821/100000000000000000000)
  centralHi := (178516276685599434411/50000000000000000000)
  directionLo := (360515880280929670999/100000000000000000000)
  directionHi := (360515880280929671/100000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree053.table
  base := (-121071332826284570136993953892796944431/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1099828850109180264497920287471044097000000000000)
      constant := (14655105280919389194217240433468598885380135000608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree053.table
  base := (-968646454061921727552581094507564164613/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1102464331218707836542963926565434847000000000000)
      constant := (14725909663436921906864680495009587626602368115948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360515880280929670999/100000000000000000000)
  centralHi := (360515880280929671/100000000000000000)
  directionLo := (90991467904520195473/25000000000000000000)
  directionHi := (363965871618080781893/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree054.table
  base := (-3459531256873317326273973198779265793333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-124508063638232863674423856856564743000000000000)
      constant := (1692005918371354016719252308484975487586598709363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree054.table
  base := (-1729896591357380730729053744949369082013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-124806419990254852962542004678571243000000000000)
      constant := (1700172845494157924238215036691574135904754753686) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90991467904520195473/25000000000000000000)
  centralHi := (363965871618080781893/100000000000000000000)
  directionLo := (183691733258933639531/50000000000000000000)
  directionHi := (367383466517867279063/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree055.table
  base := (-60397553775271896656546696679997206489/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1141316295379011281641709135947121277000000000000)
      constant := (15812161696753627108887789886750472656983572715550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree055.table
  base := (-3020103906954565143887548238320323131369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1144051228605879516782792157648847527000000000000)
      constant := (15888412255060974487414982057888609089599689465431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183691733258933639531/50000000000000000000)
  centralHi := (367383466517867279063/100000000000000000000)
  directionLo := (14830782433231797877/4000000000000000000)
  directionHi := (185384780415397473463/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree056.table
  base := (-2555369122766255147069910010888924192199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1162060018013926790213603560185159867000000000000)
      constant := (16407429323424931247078928635802787123304298180601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree056.table
  base := (-2555564436650459220815943879449548702211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1164844677299465356902706273190553867000000000000)
      constant := (16486478367890441879267114230047518866744427276989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14830782433231797877/4000000000000000000)
  centralHi := (185384780415397473463/50000000000000000000)
  directionLo := (187062504932600136089/50000000000000000000)
  directionHi := (374125009865200272179/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree057.table
  base := (-1033022785400881333424508985657969596293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-131422637849871366531721998269244273000000000000)
      constant := (1890428342636419472816779919299303217641668331846) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree057.table
  base := (-1033107074266864163490728429904641920723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-131737569554783466335846709859140023000000000000)
      constant := (1899528100351205365334718499489070236709155303306) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187062504932600136089/50000000000000000000)
  centralHi := (374125009865200272179/100000000000000000000)
  directionLo := (188725315455168763791/50000000000000000000)
  directionHi := (377450630910337527583/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree058.table
  base := (-775970484037423757700255196936679520127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1203547463283757807357392408661237047000000000000)
      constant := (17631438077266125135085539471769688628883389628546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree058.table
  base := (-776043212367610133789551734326619181429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1206431574686637037142534504273966547000000000000)
      constant := (17716234975150758972874512720556421759512722894742) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188725315455168763791/50000000000000000000)
  centralHi := (377450630910337527583/100000000000000000000)
  directionLo := (95186801390275313563/25000000000000000000)
  directionHi := (380747205561101254253/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree059.table
  base := (-1013084095873658783823840235631083733987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1224291185918673315929286832899275637000000000000)
      constant := (18260177540391789902790016573511868933871785992413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree059.table
  base := (-506604782648869217472489200631457259229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1227225023380222877262448619815672887000000000000)
      constant := (18347923832980769939962274379844828015901743059142) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95186801390275313563/25000000000000000000)
  centralHi := (380747205561101254253/100000000000000000000)
  directionLo := (192007740931559280401/50000000000000000000)
  directionHi := (384015481863118560803/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree060.table
  base := (-17979974569546619241143971249009759991/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-138337212061509869389020139681923803000000000000)
      constant := (2100008091715335932478265017011920506641947320025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree060.table
  base := (-449607561788031377195194062626514416401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-138668719119312079709151415039708803000000000000)
      constant := (2110090982231934996870171970881296391740666792311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (192007740931559280401/50000000000000000000)
  centralHi := (384015481863118560803/100000000000000000000)
  directionLo := (387256176294889823367/100000000000000000000)
  directionHi := (48407022036861227921/12500000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree061.table
  base := (138792524219710586795805969415723340423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1265778631188504333073075681375352817000000000000)
      constant := (19551123383106583101318961119585227778162498714823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree061.table
  base := (138699246848824756803718644357597025293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1268811920767394557502276850899085567000000000000)
      constant := (19644919456821511813094610754809987649210291135693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387256176294889823367/100000000000000000000)
  centralHi := (48407022036861227921/12500000000000000000)
  directionLo := (78093995120371305847/20000000000000000000)
  directionHi := (97617493900464132309/25000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree062.table
  base := (187943502826741999284281906823892548527/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1286522353823419841644970105613391407000000000000)
      constant := (20213328747529388404296010079644291048641798936508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree062.table
  base := (46980851141755851174213541920316052553/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1289605369460980397622190966440791907000000000000)
      constant := (20310225225695358800825498920965883687871908655248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78093995120371305847/20000000000000000000)
  centralHi := (97617493900464132309/25000000000000000000)
  directionLo := (19682876924784781043/5000000000000000000)
  directionHi := (393657538495695620861/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree063.table
  base := (138943020572670503934697298411809295783/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-145251786273148372246318281094603333000000000000)
      constant := (2320743169288737249181204294287266683549956086870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree063.table
  base := (347340233835229266156665296676519662051/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-145599868683840693082456120220277583000000000000)
      constant := (2331859528763953861169866869360844558195905082156) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19682876924784781043/5000000000000000000)
  centralHi := (393657538495695620861/100000000000000000000)
  directionLo := (396819497230750654181/100000000000000000000)
  directionHi := (198409748615375327091/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree064.table
  base := (2051748478076313599738894471392595714571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1328009799093250858788758954089468587000000000000)
      constant := (21571202376220897466362018936676857582968165143371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree064.table
  base := (1025844403261813644730089699179336861611/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1331192266848152077862019197524204587000000000000)
      constant := (21674450727579827441528028481006762864522178404822) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396819497230750654181/100000000000000000000)
  centralHi := (198409748615375327091/50000000000000000000)
  directionLo := (399956459068285797509/100000000000000000000)
  directionHi := (39995645906828579751/10000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree065.table
  base := (1369359058672421597274985224686530005607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1348753521728166367360653378327507177000000000000)
      constant := (22266870021203053017483015612872688543538598830414) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree065.table
  base := (2738666727058733818081955649679616588159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1351985715541737917981933313065910927000000000000)
      constant := (22373369853087446825785142243839751173189921703359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399956459068285797509/100000000000000000000)
  centralHi := (39995645906828579751/10000000000000000000)
  directionLo := (403069007638167361733/100000000000000000000)
  directionHi := (201534503819083680867/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree066.table
  base := (3450330039573773685304875904361301107141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-152166360484786875103616422507282863000000000000)
      constant := (2552632357502470909878352270574901869319650203549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree066.table
  base := (172514289587399671816772431441747886057/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-152531018248369306455760825400846363000000000000)
      constant := (2564832544346510005616591913252377424673157901460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (403069007638167361733/100000000000000000000)
  centralHi := (201534503819083680867/50000000000000000000)
  directionLo := (406157704206620541411/100000000000000000000)
  directionHi := (101539426051655135353/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree067.table
  base := (4186576540759612193256260830097642362049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1390240966997997384504442226803584357000000000000)
      constant := (23691665760769661400771762836587705669361416069249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree067.table
  base := (4186538451447421074732235942206941319173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1393572612928909598221761544149323607000000000000)
      constant := (23804819665373322039624875924127896226340294693573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406157704206620541411/100000000000000000000)
  centralHi := (101539426051655135353/25000000000000000000)
  directionLo := (81844617771572080789/20000000000000000000)
  directionHi := (204611544428930201973/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree068.table
  base := (2473725543640028119084071746576533492763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 918090000000000000000000000000000000000000000
      center := (11567934)
      previous := (5783967)
      next := (5783967)
      square := (70903509539343336705724541229780000000000000)
      linear := (-4882299964127726273620542045126723000000000000)
      constant := (84501015493391080595892335919518158926874156534) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree068.table
  base := (2473709153314505619812060267383649833891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 918090000000000000000000000000000000000000000
      center := (11567934)
      previous := (5783967)
      next := (5783967)
      square := (70903509539343336705724541229780000000000000)
      linear := (-4894000213226627814331057645989723000000000000)
      constant := (84904325197419514634331882290447745015199397638) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81844617771572080789/20000000000000000000)
  centralHi := (204611544428930201973/50000000000000000000)
  directionLo := (103066420399160547327/25000000000000000000)
  directionHi := (412265681596642189309/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree069.table
  base := (573294813814564203944296784313158007969/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-159080934696425377960914563919962393000000000000)
      constant := (2795674913440594453071248283540193411285553212410) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree069.table
  base := (5732919932366968480963044171006877381971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-159462167812897919829065530581415143000000000000)
      constant := (2809009300580318505466401202567414168634137503419) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103066420399160547327/25000000000000000000)
  centralHi := (412265681596642189309/100000000000000000000)
  directionLo := (12977686980565777579/3125000000000000000)
  directionHi := (415285983378104882529/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree070.table
  base := (6543062994244059515638376332601493823251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1452472134902743910220125499517700127000000000000)
      constant := (25912507866215032957015607384173830950415047956051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree070.table
  base := (261721549198603064964333173308193888941/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1455952959009667118581503890774442627000000000000)
      constant := (26036020712862910936037244104533756768117191343525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12977686980565777579/3125000000000000000)
  centralHi := (415285983378104882529/100000000000000000000)
  directionLo := (83656895414136724041/20000000000000000000)
  directionHi := (209142238535341810103/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree071.table
  base := (3688895835239093752475444557882908324841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1473215857537659418792019923755738717000000000000)
      constant := (26675094307603282048876983045820976412768499219282) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree071.table
  base := (1844442700292485271395390695304392369043/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1476746407703252958701418006316148967000000000000)
      constant := (26802160901542791323782903199963788858114945917772) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83656895414136724041/20000000000000000000)
  centralHi := (209142238535341810103/50000000000000000000)
  directionLo := (210630814178665996101/50000000000000000000)
  directionHi := (421261628357331992203/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree072.table
  base := (257410337103791742238854305151303344807/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-165995508908063880818212705332641923000000000000)
      constant := (3049870383940198689609027570956148009247639162336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree072.table
  base := (1029639105191514368802567173553296401313/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-166393317377426533202370235761983923000000000000)
      constant := (3064389353731800902542203549460629948275603526856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210630814178665996101/50000000000000000000)
  centralHi := (421261628357331992203/100000000000000000000)
  directionLo := (212108943289908537579/50000000000000000000)
  directionHi := (424217886579817075159/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree073.table
  base := (9121077478841096265215734185287152109761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1514703302807490435935808772231815897000000000000)
      constant := (28233725233749337169165656587912045548285018770561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree073.table
  base := (9121062050000437219889351429462801512329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1518333305090424638941246237399561647000000000000)
      constant := (28368050484673428287729609408057907437929124403529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212108943289908537579/50000000000000000000)
  centralHi := (424217886579817075159/100000000000000000000)
  directionLo := (213576842765210731637/50000000000000000000)
  directionHi := (17086147421216858531/4000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree074.table
  base := (10029629314690958167796785931112083478497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1535447025442405944507703196469854487000000000000)
      constant := (29029769577982028602763314087658859075130348680097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree074.table
  base := (5014808026139286285067010680833329440043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1539126753784010479061160352941267987000000000000)
      constant := (29167799741807719638155147290305824431400204700886) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213576842765210731637/50000000000000000000)
  centralHi := (17086147421216858531/4000000000000000000)
  directionLo := (53758680524375235109/12500000000000000000)
  directionHi := (430069444195001880873/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree075.table
  base := (10962784233948600102348154027096877818437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-172910083119702383675510846745321453000000000000)
      constant := (3315218492608646742027763604493969607430878116893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree075.table
  base := (10962772835848870990931869701517313666447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-173324466941955146575674940942552703000000000000)
      constant := (3330972433510150206383062147170220763229602069783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53758680524375235109/12500000000000000000)
  centralHi := (430069444195001880873/100000000000000000000)
  directionLo := (432965567451008144779/100000000000000000000)
  directionHi := (21648278372550407239/5000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree076.table
  base := (11920540489001867216093842400408172077001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1576934470712236961651492044945931667000000000000)
      constant := (30655315753867667865735441844895378595492824209801) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree076.table
  base := (11920530694887542120812677083338924121283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1580713651171182159300988584024680667000000000000)
      constant := (30800906918764041774880238112880571411264101703683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432965567451008144779/100000000000000000000)
  centralHi := (21648278372550407239/5000000000000000000)
  directionLo := (217921223361877450881/50000000000000000000)
  directionHi := (435842446723754901763/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree077.table
  base := (3225724149489155604699805876949656930799/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1597678193347152470223386469183970257000000000000)
      constant := (31484817499832767922738107885093714933952642551996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree077.table
  base := (12902888183565477628743282927129905514363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1601507099864767999420902699566387007000000000000)
      constant := (31634264754963893379098438681281351430661396120763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217921223361877450881/50000000000000000000)
  centralHi := (435842446723754901763/100000000000000000000)
  directionLo := (27418778787747365821/6250000000000000000)
  directionHi := (438700460603957853137/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree078.table
  base := (3477462826068090272736534445679446402167/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-179824657331340886532808988158000983000000000000)
      constant := (3591719070892620187972068279708356210357272435452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree078.table
  base := (6954922038229121894372457937965342099083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-180255616506483759948979646123121483000000000000)
      constant := (3608758375297440447723675306566179843847087004774) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27418778787747365821/6250000000000000000)
  centralHi := (438700460603957853137/100000000000000000000)
  directionLo := (110384993857323181103/25000000000000000000)
  directionHi := (441539975429292724413/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree079.table
  base := (14941403542527993933189199412037836822047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1639165638616983487367175317660047437000000000000)
      constant := (33177278140201503429184201189691908131869845463647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree079.table
  base := (1867674666872883630599464647257944844399/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1643093997251939679660730930649799687000000000000)
      constant := (33334588759346743726399767016415000035303317052792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110384993857323181103/25000000000000000000)
  centralHi := (441539975429292724413/100000000000000000000)
  directionLo := (444361345832506080773/100000000000000000000)
  directionHi := (222180672916253040387/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree080.table
  base := (639902096375475076617376172589300680447/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1659909361251898995939069741898086027000000000000)
      constant := (34040236982368481722986545680468763902086621051175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree080.table
  base := (1999693384868172256914142276323064553229/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1663887445945525519780645046191506027000000000000)
      constant := (34201554876619204960940789665554098228007831715432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444361345832506080773/100000000000000000000)
  centralHi := (222180672916253040387/50000000000000000000)
  directionLo := (17886596610335984907/4000000000000000000)
  directionHi := (111791228814599905669/25000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree081.table
  base := (1707829713897153172036263482493741475003/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-186739231542979389390107129570680513000000000000)
      constant := (3879372016023737983397822776353534253613001192670) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree081.table
  base := (8539146281208538170227531747041610715653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-187186766071012373322284351303690263000000000000)
      constant := (3897747078855865115777032927230966570686197474234) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17886596610335984907/4000000000000000000)
  centralHi := (111791228814599905669/25000000000000000000)
  directionLo := (224975508225910761099/50000000000000000000)
  directionHi := (449951016451821522199/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree082.table
  base := (3636727416395679600893483885281882556783/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1701396806521730013082858590374163207000000000000)
      constant := (35799611608509141656780030258878394375422472695915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree082.table
  base := (727345326131487395171887275201106471093/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1705474343332697200020473277274918707000000000000)
      constant := (35969095241825812153279927471222721443433070537325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224975508225910761099/50000000000000000000)
  centralHi := (449951016451821522199/100000000000000000000)
  directionLo := (22635998595931382533/5000000000000000000)
  directionHi := (452719971918627650661/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree083.table
  base := (9656785843982324966237276783242668284069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1722140529156645521654753014612201797000000000000)
      constant := (36696027360650191181820432245729416150580428494538) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree083.table
  base := (9656784157962898758606626698175159095651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1726267792026283040140387392816625047000000000000)
      constant := (36869669458776521585151309789429052102356495896902) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22635998595931382533/5000000000000000000)
  centralHi := (452719971918627650661/100000000000000000000)
  directionLo := (113868023590355101671/25000000000000000000)
  directionHi := (91094418872284081337/20000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree084.table
  base := (10234050245162679251307807945449024563931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-193653805754617892247405270983360043000000000000)
      constant := (4178177265361828299875395641761994795755309555718) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree084.table
  base := (20468097596487429026084679305091331087393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-194117915635540986695589056484259043000000000000)
      constant := (4197938483168124710366814768331616779174101341977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113868023590355101671/25000000000000000000)
  centralHi := (91094418872284081337/20000000000000000000)
  directionLo := (114551921772932922899/25000000000000000000)
  directionHi := (458207687091731691597/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree085.table
  base := (5411805773388108267566613791421714219519/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 918090000000000000000000000000000000000000000
      center := (11567934)
      previous := (5783967)
      next := (5783967)
      square := (70903509539343336705724541229780000000000000)
      linear := (-6102518942652167954320214059128993000000000000)
      constant := (133295209968283718840798067559790387143119279484) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree085.table
  base := (21647220610451963739225035896535866204119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 918090000000000000000000000000000000000000000
      center := (11567934)
      previous := (5783967)
      next := (5783967)
      square := (70903509539343336705724541229780000000000000)
      linear := (-6117144254025794880208358560207743000000000000)
      constant := (133925349137831207156570324007604403840333961271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114551921772932922899/25000000000000000000)
  centralHi := (458207687091731691597/100000000000000000000)
  directionLo := (230463522210093992521/50000000000000000000)
  directionHi := (460927044420187985043/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree086.table
  base := (5712734790607204755313975810776932761783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1784371697061392047370436287326317567000000000000)
      constant := (39452188229488563918272739108092191403935074976732) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree086.table
  base := (22850937032062575492565383971171855463537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1788648138107040560500129739441744067000000000000)
      constant := (39638608107093569966990947445006664194814789977137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230463522210093992521/50000000000000000000)
  centralHi := (460927044420187985043/100000000000000000000)
  directionLo := (231815226013039097333/50000000000000000000)
  directionHi := (463630452026078194667/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree087.table
  base := (12039624206432025282291438788683889987693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-200568379966256395104703412396039573000000000000)
      constant := (4488134780742494047099434912424907282099855737354) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree087.table
  base := (6019811646342960166393095586106589755267/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-201049065200069600068893761664827823000000000000)
      constant := (4509332551108057512460154853321794153840061339052) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231815226013039097333/50000000000000000000)
  centralHi := (463630452026078194667/100000000000000000000)
  directionLo := (46631818730763787443/10000000000000000000)
  directionHi := (466318187307637874431/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree088.table
  base := (25332150604121888783188578365168931038093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1825859142331223064514225135802394747000000000000)
      constant := (41345390066028235541182390195495597384616444988493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree088.table
  base := (25332149036651224521058553589281393378853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1830235035494212240739957970525156747000000000000)
      constant := (41540580453268589103496779704603062099523824257253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46631818730763787443/10000000000000000000)
  centralHi := (466318187307637874431/100000000000000000000)
  directionLo := (1831994217633849737/390625000000000000)
  directionHi := (468990519714265532673/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree089.table
  base := (13304822766114314413633383878854248201539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1846602864966138573086119560040433337000000000000)
      constant := (42308719342113937550122523261705537136572084361478) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree089.table
  base := (3326205523494548522690461028185675185813/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1851028484187798080859872086066863087000000000000)
      constant := (42508370581729766688543829083529580346546514817704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1831994217633849737/390625000000000000)
  centralHi := (468990519714265532673/100000000000000000000)
  directionLo := (235823855530898598327/50000000000000000000)
  directionHi := (94329542212359439331/20000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree090.table
  base := (5582346604876553124759115273913467342947/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-207482954177894897962001553808719103000000000000)
      constant := (4809244538928293833790259297933629607628006391415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree090.table
  base := (27911731871672357970495341288207592917307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-207980214764598213442198466845396603000000000000)
      constant := (4831929260100972847344940005826710529395990676323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235823855530898598327/50000000000000000000)
  centralHi := (94329542212359439331/20000000000000000000)
  directionLo := (14821562994746355391/3125000000000000000)
  directionHi := (474290015831883372513/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree091.table
  base := (29238412934213937594903451351315835895083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1888090310235969590229908408516510517000000000000)
      constant := (44268834586866740727108109539272086413952894117483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree091.table
  base := (29238411945889383975956200326081277031833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1892615381574969761099700317150275767000000000000)
      constant := (44477558727040292761803349751508570772811495654233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14821562994746355391/3125000000000000000)
  centralHi := (474290015831883372513/100000000000000000000)
  directionLo := (119229420364109332367/25000000000000000000)
  directionHi := (476917681456437329469/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree092.table
  base := (3058968513776216296382569422684459600451/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1908834032870885098801802832754549107000000000000)
      constant := (45265620548361220690663326666822183062713058932510) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree092.table
  base := (1223587371619320904364550463751510650641/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1913408830268555601219614432691982107000000000000)
      constant := (45478956736937140138663340848567812952570954386025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119229420364109332367/25000000000000000000)
  centralHi := (476917681456437329469/100000000000000000000)
  directionLo := (119882737147013652363/25000000000000000000)
  directionHi := (479530948588054609453/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree093.table
  base := (31965549530067971196789948831431559851011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-214397528389533400819299695221398633000000000000)
      constant := (5141506525783690627782226595403695872349607167979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree093.table
  base := (6393109760758245851195804130467829428749/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-214911364329126826815503172025965383000000000000)
      constant := (5165728596433546550854260141405593150463856053305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119882737147013652363/25000000000000000000)
  centralHi := (479530948588054609453/100000000000000000000)
  directionLo := (120532512839310062099/25000000000000000000)
  directionHi := (482130051357240248397/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree094.table
  base := (33366006022280645548386105820778158547567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1950321478140716115945591681230626287000000000000)
      constant := (47292649135585267219124913520084811366389044245167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree094.table
  base := (33366005399797568003874290416629260080621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1954995727655727281459442663775394787000000000000)
      constant := (47515360617652372242078020575186755181496360949421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120532512839310062099/25000000000000000000)
  centralHi := (482130051357240248397/100000000000000000000)
  directionLo := (96943043523444376319/20000000000000000000)
  directionHi := (121178804404305470399/25000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree095.table
  base := (3479105453920588324196945864092678711293/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1971065200775631624517486105468664877000000000000)
      constant := (48322891756962259926011487704477275713036736216930) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree095.table
  base := (17395527002871740966912650426807535185779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-1975789176349313121579356779317101127000000000000)
      constant := (48550366484258011680054061325270069170269544473958) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96943043523444376319/20000000000000000000)
  centralHi := (121178804404305470399/25000000000000000000)
  directionLo := (487286669177073232579/100000000000000000000)
  directionHi := (24364333458853661629/5000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree096.table
  base := (9060173754306532657458849653677035223379/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-221312102601171903676597836634078163000000000000)
      constant := (5484920732721804653295376824777383276378624690924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree096.table
  base := (2265043410006518610535761156109241038803/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-221842513893655440188807877206534163000000000000)
      constant := (5510730551787379484328989941661521748877499159472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487286669177073232579/100000000000000000000)
  centralHi := (24364333458853661629/5000000000000000000)
  directionLo := (489844622023823038749/100000000000000000000)
  directionHi := (391875697619058431/80000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree097.table
  base := (9428731850634246667388150114996180735461/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2012552646045462641661274953944742057000000000000)
      constant := (50416833646759631614282601765765109628356081425044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree097.table
  base := (3771492701087358335753190090237583342379/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2017376073736484801819185010400513807000000000000)
      constant := (50653986061757706963827143655682089951942568735790) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489844622023823038749/100000000000000000000)
  centralHi := (391875697619058431/80000000000000000)
  directionLo := (492389286534178874257/100000000000000000000)
  directionHi := (246194643267089437129/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree098.table
  base := (19606875824825832405506676299271033741587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2033296368680378150233169378182780647000000000000)
      constant := (51480532912545537274220634292913095780159626590374) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree098.table
  base := (9803437828527226841596501009786600168477/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2038169522430070641939099125942220147000000000000)
      constant := (51722599770105970708603127590765313909947066856308) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492389286534178874257/100000000000000000000)
  centralHi := (246194643267089437129/50000000000000000000)
  directionLo := (494920867676453254351/100000000000000000000)
  directionHi := (30932554229778328397/6250000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree099.table
  base := (20368583860066397326418205842176740941547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-228226676812810406533895978046757693000000000000)
      constant := (5839487154537123084405483372178634174051248707366) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree099.table
  base := (20368583716349599024636194784032261703387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-228773663458184053562112582387102943000000000000)
      constant := (5866935121127393990195464405722872112245752954886) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494920867676453254351/100000000000000000000)
  centralHi := (30932554229778328397/6250000000000000000)
  directionLo := (497439565203240541511/100000000000000000000)
  directionHi := (62179945650405067689/12500000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree100.table
  base := (21142587790758514371107435626495746789993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2074783813950209167376958226658857827000000000000)
      constant := (53641388080763999532809567395202677278850546120786) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree100.table
  base := (8457035067063991493980956378118459441841/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2079756419817242322178927357025632827000000000000)
      constant := (53893435021048305903126905408416533143984691633205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (497439565203240541511/100000000000000000000)
  centralHi := (62179945650405067689/12500000000000000000)
  directionLo := (499945573835357246887/100000000000000000000)
  directionHi := (62493196729419655861/12500000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree101.table
  base := (43857775206403164800506910764796227966843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (327726)
      previous := (163863)
      next := (163863)
      square := (2008735835395571444755846722420000000000000)
      linear := (-205423736553781460243981242123017000000000000)
      constant := (5365997841545748646846518523188069488941758643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree101.table
  base := (5482221874443465577779653244904779570149/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (327726)
      previous := (163863)
      next := (163863)
      square := (2008735835395571444755846722420000000000000)
      linear := (-205916073768339198343186106515767000000000000)
      constant := (5391202486237639667689601778195013153295660392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499945573835357246887/100000000000000000000)
  centralHi := (62493196729419655861/12500000000000000000)
  directionLo := (502439083437525081883/100000000000000000000)
  directionHi := (125609770859381270471/25000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree102.table
  base := (22727483285839471033217641763805382579101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7878167726593704078413837914420000000000000)
      linear := (-813637546797401070557765119236807000000000000)
      constant := (21471300304787936172712640075668303915378818602) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree102.table
  base := (4545496639110953598958433429255015998957/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1285326)
      previous := (642663)
      next := (642663)
      square := (7878167726593704078413837914420000000000000)
      linear := (-815587588313884660676184386047307000000000000)
      constant := (21572118690019665837760427942600913182053603570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (502439083437525081883/100000000000000000000)
  centralHi := (125609770859381270471/25000000000000000000)
  directionLo := (504920279186245338409/100000000000000000000)
  directionHi := (50492027918624533841/10000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree103.table
  base := (23538374828932721656372041871909723414161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2137014981854955693092641499372973597000000000000)
      constant := (56966312413682889414556038815915079623625948789922) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree103.table
  base := (47076749503246824208929007711921077042039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2142136765897999842538669703650751847000000000000)
      constant := (57233707472443554349978613974326228438362089421239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504920279186245338409/100000000000000000000)
  centralHi := (50492027918624533841/10000000000000000000)
  directionLo := (253694670865142328843/50000000000000000000)
  directionHi := (507389341730284657687/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree104.table
  base := (4872312444856123399648398949915510401403/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2157758704489871201664535923611012187000000000000)
      constant := (58096924943961408235630121080910770420938559198030) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree104.table
  base := (24361562158088162795370210141134872249917/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2162930214591585682658583819192458187000000000000)
      constant := (58369536840798598573388003238329939387134940055034) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253694670865142328843/50000000000000000000)
  centralHi := (507389341730284657687/100000000000000000000)
  directionLo := (254923223672082900321/50000000000000000000)
  directionHi := (509846447344165800643/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree105.table
  base := (25197045464985541977821260198283520542041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-242055825236087412248492260872116753000000000000)
      constant := (6582076631469216927978883192212109309082530219298) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree105.table
  base := (2519704540831661041949417892639056111901/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-242635962587241280308721992748240503000000000000)
      constant := (6612952090828258967062279012073905398377562143780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254923223672082900321/50000000000000000000)
  centralHi := (509846447344165800643/100000000000000000000)
  directionLo := (256145884037516244469/50000000000000000000)
  directionHi := (512291768075032488939/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree106.table
  base := (26044824545253209430501118316624863470553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2199246149759702218808324772087089367000000000000)
      constant := (60391606631160044426544686946892401307732704217906) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree106.table
  base := (52089648993483982953166445760304506616797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2204517111978757362898412050275870867000000000000)
      constant := (60674803402115347084163575047163036380466658058397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256145884037516244469/50000000000000000000)
  centralHi := (512291768075032488939/100000000000000000000)
  directionLo := (514725471883234590797/100000000000000000000)
  directionHi := (257362735941617295399/50000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree107.table
  base := (6726224865055825107644619813341572261381/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2219989872394617727380219196325127957000000000000)
      constant := (61555675787514768710129907995645131798706736465448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree107.table
  base := (53809798837398313465321189823710372631697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2225310560672343203018326165817577207000000000000)
      constant := (61844240594534088762676380115461035130172662793297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514725471883234590797/100000000000000000000)
  centralHi := (257362735941617295399/50000000000000000000)
  directionLo := (258573861388479370081/50000000000000000000)
  directionHi := (517147722776958740163/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree108.table
  base := (55554540411651793605344494875723660289891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-248970399447725915105790402284796283000000000000)
      constant := (6970099683563461393833141384476812608940364468299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree108.table
  base := (11110908068114233000300207048424984903987/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-249567112151769893682026697928809283000000000000)
      constant := (7002764488278162885592255236265218420603050654215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258573861388479370081/50000000000000000000)
  centralHi := (517147722776958740163/100000000000000000000)
  directionLo := (103911736188241954747/20000000000000000000)
  directionHi := (64944835117651221717/12500000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree109.table
  base := (57323873557319571116782405026920985621529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2261477317664448744524008044801205137000000000000)
      constant := (63917270724648708514890581221090606654719890272729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree109.table
  base := (5732387349648721885451160511189566826609/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2266897458059514883258154396900989887000000000000)
      constant := (64216722801850609052415760409237220549366181018090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103911736188241954747/20000000000000000000)
  centralHi := (64944835117651221717/12500000000000000000)
  directionLo := (52195850286143003173/10000000000000000000)
  directionHi := (521958502861430031731/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree110.table
  base := (2955889917588931050253517297496338034741/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2282221040299364253095902469039243727000000000000)
      constant := (65114796505096960818243507666616385738590280790820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree110.table
  base := (3694862393732584267609586012353680450567/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2287690906753100723378068512442696227000000000000)
      constant := (65419767816431574200671598591313017765199752770672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52195850286143003173/10000000000000000000)
  centralHi := (521958502861430031731/100000000000000000000)
  directionLo := (20973893657681059543/4000000000000000000)
  directionHi := (2048231802507915971/390625000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree111.table
  base := (30468157395156951318829243742187486384209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-255884973659364417963088543697475813000000000000)
      constant := (7369274943698978468860743670071095692093872653202) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree111.table
  base := (30468157372884791681582861438986597395299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-256498261716298507055331403109378063000000000000)
      constant := (7403779493125206497499873020562794643357019267222) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20973893657681059543/4000000000000000000)
  centralHi := (2048231802507915971/390625000000000000)
  directionLo := (131681336530014940533/25000000000000000000)
  directionHi := (526725346120059762133/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree112.table
  base := (15694855717254619401704880150803642090721/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2323708485569195270239691317515320907000000000000)
      constant := (67543304689126582700108651760480783906673296958084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree112.table
  base := (31389711415452964199791093910521804679677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2329277804140272403617896743526108907000000000000)
      constant := (67859465666837600780484696712234115403453477170554) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131681336530014940533/25000000000000000000)
  centralHi := (526725346120059762133/100000000000000000000)
  directionLo := (21163706518973368223/4000000000000000000)
  directionHi := (66136582871791775697/12500000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree113.table
  base := (16161780646166989107008506755471630650591/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2344452208204110778811585741753359497000000000000)
      constant := (68774287092518738174790137550159187792290526141564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree113.table
  base := (64647122552061090831539817216630928340543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2350071252833858243737810859067815247000000000000)
      constant := (69096118502482364180938105952500640080604887650943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21163706518973368223/4000000000000000000)
  centralHi := (66136582871791775697/12500000000000000000)
  directionLo := (531449434830114433537/100000000000000000000)
  directionHi := (265724717415057216769/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree114.table
  base := (66539413934614121648271024549631296106023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-262799547871002920820386685110155343000000000000)
      constant := (7779602411488556446345016944708122887605909240047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree114.table
  base := (16634853476679945216982990527830047916683/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-263429411280827120428636108289946843000000000000)
      constant := (7815997104999378999486035624378545379530584275148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531449434830114433537/100000000000000000000)
  centralHi := (265724717415057216769/50000000000000000000)
  directionLo := (66724475169960087383/12500000000000000000)
  directionHi := (106759160271936139813/20000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree115.table
  base := (2139259278646712818364703326237938113191/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2385939653473941795955374590229436677000000000000)
      constant := (71269708521704023984326223950250111529443592895712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree115.table
  base := (2738251875713349993669099440453730870827/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2391658150221029923977639090151227927000000000000)
      constant := (71603031994319395449512488307559932940080237410675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66724475169960087383/12500000000000000000)
  centralHi := (106759160271936139813/20000000000000000000)
  directionLo := (134032974794730863017/25000000000000000000)
  directionHi := (536131899178923452069/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree116.table
  base := (2815910861166303239996985717412728213353/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2406683376108857304527269014467475267000000000000)
      constant := (72534147547393288906907434462118673990799517293825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree116.table
  base := (70397771508748166667382278962260870025101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2412451598914615764097553205692934267000000000000)
      constant := (72873292650413410239471253170816456676462869837901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134032974794730863017/25000000000000000000)
  centralHi := (536131899178923452069/100000000000000000000)
  directionLo := (538457861940166110659/100000000000000000000)
  directionHi := (26922893097008305533/5000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree117.table
  base := (72363837770595070070955753464415403536333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-269714122082641423677684826522834873000000000000)
      constant := (8201082086714162386169855526756848501096024417637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree117.table
  base := (7236383775313929745503913935417497264599/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-270360560845355733801940813470515623000000000000)
      constant := (8239417323693481444152675351160463999432944013110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (538457861940166110659/100000000000000000000)
  centralHi := (26922893097008305533/5000000000000000000)
  directionLo := (270386910210697253249/50000000000000000000)
  directionHi := (540773820421394506499/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree118.table
  base := (37177247819945126803636196161868756700807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2448170821378688321671057862943552447000000000000)
      constant := (75096482220776903920165046162284534797819857340814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree118.table
  base := (9294311953120220417299902483323448239041/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2454038496301787444337381436776346947000000000000)
      constant := (75447421782775426893791850353958934407082202270728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270386910210697253249/50000000000000000000)
  centralHi := (540773820421394506499/100000000000000000000)
  directionLo := (543079902612061571247/100000000000000000000)
  directionHi := (33942493913253848203/6250000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree119.table
  base := (2386554535505315958339273919665327665149/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 918090000000000000000000000000000000000000000
      center := (11567934)
      previous := (5783967)
      next := (5783967)
      square := (70903509539343336705724541229780000000000000)
      linear := (-8542956899701051315719558087133533000000000000)
      constant := (264340407849198797750495097085286427163509265312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree119.table
  base := (19092436280850978593131470021209728634061/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 918090000000000000000000000000000000000000000
      center := (11567934)
      previous := (5783967)
      next := (5783967)
      square := (70903509539343336705724541229780000000000000)
      linear := (-8563432335624129011962960388643783000000000000)
      constant := (265575398820048984713681331881072685404658025396) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (543079902612061571247/100000000000000000000)
  centralHi := (33942493913253848203/6250000000000000000)
  directionLo := (34086014612226660293/6250000000000000000)
  directionHi := (545376233795626564689/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree120.table
  base := (3920479312938320290591819095487844286551/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-276628696294279926534982967935514403000000000000)
      constant := (8633713969259375245202065751470931377497877020780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree120.table
  base := (15681917249570016028156402822784123743579/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-277291710409884347175245518651084403000000000000)
      constant := (8674040149097909622457113602169911982915420352655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34086014612226660293/6250000000000000000)
  centralHi := (545376233795626564689/100000000000000000000)
  directionLo := (109532587325795892299/20000000000000000000)
  directionHi := (68457867078622432687/12500000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree121.table
  base := (8047401900718250685178142266823082343049/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2510401989283434847386741135657668217000000000000)
      constant := (79023625785511500847862703784492145909647328502490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree121.table
  base := (80474018997848646568685416325779128781151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2516418842382544964697123783401465967000000000000)
      constant := (79392635031424534367005167331686314318403652033951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109532587325795892299/20000000000000000000)
  centralHi := (68457867078622432687/12500000000000000000)
  directionLo := (21997605248755718863/4000000000000000000)
  directionHi := (68742516402361621447/12500000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree122.table
  base := (2064076084526632942253753516832166154997/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2531145711918350355958635559895706807000000000000)
      constant := (80354978054940454844562000159231910411078822263880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree122.table
  base := (82563043373085068541395740268229300844483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2537212291076130804817037898943172307000000000000)
      constant := (80730111327615854113989758590914441060675799386883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21997605248755718863/4000000000000000000)
  centralHi := (68742516402361621447/12500000000000000000)
  directionLo := (883532696313019249/160000000000000000)
  directionHi := (276103967597818515313/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree123.table
  base := (84676659380181546171585885896573798616141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-283543270505918429392281109348193933000000000000)
      constant := (9077498059068338811398171312025422917388460504549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree123.table
  base := (84676659373359063639311201589136943176373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-284222859974412960548550223831653183000000000000)
      constant := (9119865581161092421053855950417055293171890301197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (883532696313019249/160000000000000000)
  centralHi := (276103967597818515313/50000000000000000000)
  directionLo := (554466463783883427817/100000000000000000000)
  directionHi := (277233231891941713909/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree124.table
  base := (86814867004397645460381335185752217340303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2572633157188181373102424408371783987000000000000)
      constant := (83051139215531740850311326632039101860999008778703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree124.table
  base := (86814866998565347354810422819789488091783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2578799188463302485056866130026584987000000000000)
      constant := (83438671739923673900600901228480249767431148074183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554466463783883427817/100000000000000000000)
  centralHi := (277233231891941713909/50000000000000000000)
  directionLo := (556715829871021504181/100000000000000000000)
  directionHi := (278357914935510752091/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree125.table
  base := (44488833126831434044203855942607732523771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2593376879823096881674318832609822577000000000000)
      constant := (84415948106689183015272239957286146088728887425142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree125.table
  base := (88977666248677367679409175849505258728007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2599592637156888325176780245568291327000000000000)
      constant := (84809755856036675948181089278995374540783722857607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556715829871021504181/100000000000000000000)
  centralHi := (278357914935510752091/50000000000000000000)
  directionLo := (558956144072999528343/100000000000000000000)
  directionHi := (69869518009124941043/12500000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree126.table
  base := (45582528563997478565940724847377879807829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-290457844717556932249579250760873463000000000000)
      constant := (9532434356120871841219628916917357733109565577562) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree126.table
  base := (11395632140466697452792841408840103437797/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-291154009538941573921854929012221963000000000000)
      constant := (9576893619865539805703640033567682626630652159464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558956144072999528343/100000000000000000000)
  centralHi := (69869518009124941043/12500000000000000000)
  directionLo := (140296878699450102067/25000000000000000000)
  directionHi := (561187514797800408269/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree127.table
  base := (93377039627468071332456364798513487097127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2634864325092927898818107681085899757000000000000)
      constant := (87179022510729699156559298632653698607964138362727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree127.table
  base := (93377039623825870300529498929950584397557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2641179534544060005416608476651704007000000000000)
      constant := (87585531908185658832643574199515563917154084767157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140296878699450102067/25000000000000000000)
  centralHi := (561187514797800408269/100000000000000000000)
  directionLo := (563410048306654803001/100000000000000000000)
  directionHi := (281705024153327401501/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree128.table
  base := (2987925429756331323081260349875226886089/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2655608047727843407390002105323938347000000000000)
      constant := (88577288023617935099671015154200884569550371369248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree128.table
  base := (95613613749089804643409469481276957977833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (3343132926)
      previous := (1671566463)
      next := (1671566463)
      square := (20491114256870224307954392415406420000000000000)
      linear := (-2661972983237645845536522592193410347000000000000)
      constant := (88990223844227674609408941284681264287911205400233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell071.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (563410048306654803001/100000000000000000000)
  centralHi := (281705024153327401501/50000000000000000000)
  directionLo := (70702981096636179193/12500000000000000000)
  directionHi := (113124769754617886709/20000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree129.table
  base := (3058586859448643571196032069672724453767/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-297372418929195435106877392173552993000000000000)
      constant := (9998522860417416417078686941316107741489808040416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 5227
  qDenominator := 10302
  table := BinomialMassData.Q5227_10302.Degree129.table
  base := (97874779499696412109774044189810774831331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (371459214)
      previous := (185729607)
      next := (185729607)
      square := (2276790472985580478661599157267380000000000000)
      linear := (-298085159103470187295159634192790743000000000000)
      constant := (10045124265213382608024901278653842061861723776459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5227_10302.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell071.Kernel129
