import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell114.Parameters
import ForestUnimodality.BinomialMassData.Q1531_2926.Batch000_049
import ForestUnimodality.BinomialMassData.Q1531_2926.Batch050_099
import ForestUnimodality.BinomialMassData.Q1531_2926.Batch100_149
import ForestUnimodality.BinomialMassData.Q11_21.Batch000_049
import ForestUnimodality.BinomialMassData.Q11_21.Batch050_099
import ForestUnimodality.BinomialMassData.Q11_21.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree000.table
  base := (4991399443977042109764852249/100000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000
      center := (2)
      previous := (1)
      next := (1)
      square := (18159377909245888460532114600000000000)
      linear := (-956265862610000162702394980000000000)
      constant := (9982798887954084219529704498000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree000.table
  base := (4991399443977042109764852249/100000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000
      center := (2)
      previous := (1)
      next := (1)
      square := (18159377909245888460532114600000000000)
      linear := (-956265862610000162702394980000000000)
      constant := (9982798887954084219529704498000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree001.table
  base := (278193564275699745203355151123958310868359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-2136054944812341722211570046205071000000000000)
      constant := (596022489269288476633043764091988106874998684471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree001.table
  base := (277954055515026969222360715514537030394447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-146855763991376842341959885523000000000000)
      constant := (40899549196396992184708835832419943467983709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49943278484292930809/100000000000000000000)
  directionHi := (4994327848429293081/10000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree002.table
  base := (162770471532647281384900283308198427772397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-4169771799220248272510981970362761000000000000)
      constant := (350624209812095653943330972652738787652777594493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree002.table
  base := (16252125922413263935208766692462341168353/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 147000000000000000000000000000000000000000
      center := (1470)
      previous := (735)
      next := (735)
      square := (13347142763295728018491104231000000000000)
      linear := (-28668297389257018348805716794300000000000)
      constant := (2404447400155751181959132120370564151747891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49943278484292930809/100000000000000000000)
  centralHi := (4994327848429293081/10000000000000000000)
  directionLo := (35315230890931728327/50000000000000000000)
  directionHi := (14126092356372691331/20000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree003.table
  base := (1578759486738763909806910381113631848737/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-3101744326814077411405196947260225500000000000)
      constant := (110606686845132418229218676195492967766379646496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree003.table
  base := (100842043377479989176905968035213107640027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (4900)
      previous := (2450)
      next := (2450)
      square := (44490475877652426728303680770000000000000)
      linear := (-142170061264587841544718150121000000000000)
      constant := (5054805985418505595481015947728442274361323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35315230890931728327/50000000000000000000)
  centralHi := (14126092356372691331/20000000000000000000)
  directionLo := (43252147915678452363/50000000000000000000)
  directionHi := (86504295831356904727/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree004.table
  base := (13368415241208342170288591005642000242027/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4280738000000000000000000000000000000000000000
      center := (42807380)
      previous := (21403690)
      next := (21403690)
      square := (388677695362347130383806615942874000000000000)
      linear := (-1647441101607212274621961163735628200000000000)
      constant := (30358774404774506135040502827014945216027087963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree004.table
  base := (33348506781458036895777036591673809919619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (7350)
      previous := (3675)
      next := (3675)
      square := (66735713816478640092455521155000000000000)
      linear := (-283168696847478432890125866391500000000000)
      constant := (5202565040952262092095284269202050058183993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43252147915678452363/50000000000000000000)
  centralHi := (86504295831356904727/100000000000000000000)
  directionLo := (49943278484292930809/50000000000000000000)
  directionHi := (99886556968585861619/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree005.table
  base := (46938487662222378669060785521975532764649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-10270922362443967923409217742835831000000000000)
      constant := (114034943770353169359396806594130804087939015481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree005.table
  base := (46834714594133937382166095825972363021937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-706164603596150206926349015203000000000000)
      constant := (7818646466117411508195597967532937364224739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49943278484292930809/50000000000000000000)
  centralHi := (99886556968585861619/100000000000000000000)
  directionLo := (111676565710081656061/100000000000000000000)
  directionHi := (55838282855040828031/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree006.table
  base := (4325385446788094098396540200183656641701/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-6152319608425937236854314833496760500000000000)
      constant := (46769422376308017402659222040377302430163710676) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree006.table
  base := (34527715813004725319281485420911427449479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (4900)
      previous := (2450)
      next := (2450)
      square := (44490475877652426728303680770000000000000)
      linear := (-281997271165781182690815432541000000000000)
      constant := (2138678267383079042642478400290659945024471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111676565710081656061/100000000000000000000)
  centralHi := (55838282855040828031/50000000000000000000)
  directionLo := (122335548368239324001/100000000000000000000)
  directionHi := (61167774184119662001/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree007.table
  base := (3299553177336852728476746553274939485239/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (2184050)
      previous := (1092025)
      next := (1092025)
      square := (19830494661344241346112582446065000000000000)
      linear := (-146309755829181439020490220317869500000000000)
      constant := (846366401809742208917621159502794526618899036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree007.table
  base := (26339665638845621306154384282553491285329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (300)
      previous := (150)
      next := (150)
      square := (2723906686386883269079817190000000000000)
      linear := (-20118755579561977330990685307000000000000)
      constant := (116166355257951572403355901196660473855987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122335548368239324001/100000000000000000000)
  centralHi := (61167774184119662001/50000000000000000000)
  directionLo := (26427498905736396089/20000000000000000000)
  directionHi := (66068747264340990223/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree008.table
  base := (20540602876634502808740838900129885184619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-16372072925667687574307453515308901000000000000)
      constant := (78444747513519355050597562812404170222717784411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree008.table
  base := (10247947425890943923507513842544457262927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (7350)
      previous := (3675)
      next := (3675)
      square := (66735713816478640092455521155000000000000)
      linear := (-562823116649865115182320431231500000000000)
      constant := (2693059953633497427914227213066035217650269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26427498905736396089/20000000000000000000)
  centralHi := (66068747264340990223/50000000000000000000)
  directionLo := (35315230890931728327/25000000000000000000)
  directionHi := (141260923563726913309/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree009.table
  base := (16100838960458331836509543083714541051739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-18405789780075594124606865439466591000000000000)
      constant := (78040597474797349247185002227057777516369551691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree009.table
  base := (16064081011508308787022435890291376600049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (4900)
      previous := (2450)
      next := (2450)
      square := (44490475877652426728303680770000000000000)
      linear := (-421824481066974523836912714961000000000000)
      constant := (1786962967435491259119285660613277453402401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35315230890931728327/25000000000000000000)
  centralHi := (141260923563726913309/100000000000000000000)
  directionLo := (149829835452878792427/100000000000000000000)
  directionHi := (37457458863219698107/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree010.table
  base := (12572770636208523403869021766959836758759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-20439506634483500674906277363624281000000000000)
      constant := (80651934258559527655319740963523793843508242071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree010.table
  base := (3135373126033499552657962784955543587963/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (7350)
      previous := (3675)
      next := (3675)
      square := (66735713816478640092455521155000000000000)
      linear := (-702650326551058456328417713651500000000000)
      constant := (2771278422758051791383783717641929814861122) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149829835452878792427/100000000000000000000)
  centralHi := (37457458863219698107/25000000000000000000)
  directionLo := (78967256913223805931/50000000000000000000)
  directionHi := (157934513826447611863/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree011.table
  base := (604617246208108398545720393852754717571/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88445000000000000000000000000000000000000000
      center := (884450)
      previous := (442225)
      next := (442225)
      square := (8030530895916263024458814378985000000000000)
      linear := (-92864559871452095971924335899925500000000000)
      constant := (354025027314266673745609580724614025592907352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree011.table
  base := (9646615097247531462574093701286311280607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-1545127863003310253802932709723000000000000)
      constant := (5889741144731404847733016365802087758249229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78967256913223805931/50000000000000000000)
  centralHi := (157934513826447611863/100000000000000000000)
  directionLo := (8282155776631469679/5000000000000000000)
  directionHi := (165643115532629393581/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree012.table
  base := (1809433284579090307910422709309204855441/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-12253470171649656887752550605969830500000000000)
      constant := (46375380307117727156321848496211097974470795458) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree012.table
  base := (721361967301942675245835946243994854259/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49000000000000000000000000000000000000000
      center := (490)
      previous := (245)
      next := (245)
      square := (4449047587765242672830368077000000000000)
      linear := (-56165169096816786498300999738100000000000)
      constant := (212602163987714791635558518963155747858691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8282155776631469679/5000000000000000000)
  centralHi := (165643115532629393581/100000000000000000000)
  directionLo := (43252147915678452363/25000000000000000000)
  directionHi := (173008591662713809453/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree013.table
  base := (5160129814455087468711863507431838234931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-26540657197707220325804513136097351000000000000)
      constant := (101658993240679282930390242797286599171061029539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree013.table
  base := (1284657416648228777782722800937849369229/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (7350)
      previous := (3675)
      next := (3675)
      square := (66735713816478640092455521155000000000000)
      linear := (-912391141402848468047563637281500000000000)
      constant := (3496129157591137624151591366645227714553326) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43252147915678452363/25000000000000000000)
  centralHi := (173008591662713809453/100000000000000000000)
  directionLo := (22509131429986948829/12500000000000000000)
  directionHi := (180073051439895590633/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree014.table
  base := (1685680134425191603144133140751764370689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (2184050)
      previous := (1092025)
      next := (1092025)
      square := (19830494661344241346112582446065000000000000)
      linear := (-291575245429746192613305357757704500000000000)
      constant := (1145403658901476474514405517552078319476066209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree014.table
  base := (419015530330449608936078900066325352237/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (1361953343193441634539908595000000000000)
      linear := (-20047035639866227318788005683500000000000)
      constant := (78796956822359312187532126259795904226844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22509131429986948829/12500000000000000000)
  centralHi := (180073051439895590633/100000000000000000000)
  directionLo := (1868706368604626997/1000000000000000000)
  directionHi := (186870636860462699701/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree015.table
  base := (1821787785382273831815579844220854205961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-30608090906523033426403336984412731000000000000)
      constant := (124416215720786695087207774513451685495958539609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree015.table
  base := (360913260500613089942351152969782031959/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98000000000000000000000000000000000000000
      center := (980)
      previous := (490)
      next := (490)
      square := (8898095175530485345660736154000000000000)
      linear := (-140295780173872241225821455960200000000000)
      constant := (570687555090266667964675893818519319565991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1868706368604626997/1000000000000000000)
  centralHi := (186870636860462699701/100000000000000000000)
  directionLo := (48357371456166430717/25000000000000000000)
  directionHi := (193429485824665722869/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree016.table
  base := (3793259495435076517379814936623291647/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 856147600000000000000000000000000000000000000
      center := (8561476)
      previous := (4280738)
      next := (4280738)
      square := (77735539072469426076761323188574800000000000)
      linear := (-1305672310437237599068109956342816840000000000)
      constant := (5523169015795897394678186176981751130595988715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree016.table
  base := (458754209367608348890308619654344723709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-2244263912509276959533419121823000000000000)
      constant := (9501424347860491786533389262017188674385223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48357371456166430717/25000000000000000000)
  centralHi := (193429485824665722869/100000000000000000000)
  directionLo := (49943278484292930809/25000000000000000000)
  directionHi := (199773113937171723237/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree017.table
  base := (-700629220602101761450271246995431149323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-34675524615338846527002160832728111000000000000)
      constant := (153176306186990274487216263150297553026354679813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree017.table
  base := (-714381353193425869631393842503219140487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-2384091122410470300679516404243000000000000)
      constant := (10541161643595382134085515447383026786348411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49943278484292930809/25000000000000000000)
  centralHi := (199773113937171723237/100000000000000000000)
  directionLo := (41184282496075530003/20000000000000000000)
  directionHi := (6435044140011801563/3125000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree018.table
  base := (-345188400997875373934536952895179826357/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4280738000000000000000000000000000000000000000
      center := (42807380)
      previous := (21403690)
      next := (21403690)
      square := (388677695362347130383806615942874000000000000)
      linear := (-7341848293949350615460314551377160200000000000)
      constant := (33931487612711852775353985206594897450240094267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree018.table
  base := (-869096529698695472896192468541585196667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (2450)
      previous := (1225)
      next := (1225)
      square := (22245237938826213364151840385000000000000)
      linear := (-420653055385277273637602281110500000000000)
      constant := (1946015395074786677059246511000462325363317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41184282496075530003/20000000000000000000)
  centralHi := (6435044140011801563/3125000000000000000)
  directionLo := (211891385345590369963/100000000000000000000)
  directionHi := (52972846336397592491/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree019.table
  base := (-2620898449293568814778839655221524204067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (592900)
      previous := (296450)
      next := (296450)
      square := (5383347581195943634124745373170000000000000)
      linear := (-107321214194334237195570594684331000000000000)
      constant := (519339895981949832249655138983505582994086757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree019.table
  base := (-526357369326402032224252563817024462613/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294000000000000000000000000000000000000000
      center := (2940)
      previous := (1470)
      next := (1470)
      square := (26694285526591456036982208462000000000000)
      linear := (-532749108442571396594342193816600000000000)
      constant := (2580681591124902049791715237818297403995889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211891385345590369963/100000000000000000000)
  centralHi := (52972846336397592491/25000000000000000000)
  directionLo := (108848851911071053997/50000000000000000000)
  directionHi := (43539540764428421599/20000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree020.table
  base := (-340132152895417585328805502100906966649/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2140369000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (194338847681173565191903307971437000000000000)
      linear := (-4077667517856256617790039660520118100000000000)
      constant := (20661523233864568773947500206395980856700446519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree020.table
  base := (-27287811247604976972143458087766549877/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58800000000000000000000000000000000000000
      center := (588)
      previous := (294)
      next := (294)
      square := (5338857105318291207396441692400000000000)
      linear := (-112142910084562012964712330060120000000000)
      constant := (568831351461516476753100832603891585840405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108848851911071053997/50000000000000000000)
  centralHi := (43539540764428421599/20000000000000000000)
  directionLo := (111676565710081656061/50000000000000000000)
  directionHi := (223353131420163312123/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree021.table
  base := (-4080402780108989992892925796421906721733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4368100)
      previous := (2184050)
      next := (2184050)
      square := (39660989322688482692225164892130000000000000)
      linear := (-873681470060621892412240990395079000000000000)
      constant := (4633261081143529571981743366901593692487980827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree021.table
  base := (-4088944790036347910807463405788059114173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (100)
      previous := (50)
      next := (50)
      square := (907968895462294423026605730000000000000)
      linear := (-20023128993300977314720445809000000000000)
      constant := (106301237785336777364898147163211940885827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111676565710081656061/50000000000000000000)
  centralHi := (223353131420163312123/100000000000000000000)
  directionLo := (228868854108531729137/100000000000000000000)
  directionHi := (114434427054265864569/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree022.table
  base := (-4669188769726273521886891549026333669729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (1768900)
      previous := (884450)
      next := (884450)
      square := (16061061791832526048917628757970000000000000)
      linear := (-370612470143622969243795210359641000000000000)
      constant := (2055386286216118848919706057536430183716163719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree022.table
  base := (-4676730269012209016887573925910876375699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-3083227171916437006410002816343000000000000)
      constant := (17118279833636209151675132144937101172772247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228868854108531729137/100000000000000000000)
  centralHi := (114434427054265864569/50000000000000000000)
  directionLo := (46850948099995593639/20000000000000000000)
  directionHi := (58563685124994492049/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree023.table
  base := (-5176954713345626997331474474823628719027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-46877825741786285828798632377674251000000000000)
      constant := (271611222923188703511294812814016632622284899037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree023.table
  base := (-2591799887186353692434775542164720588531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (7350)
      previous := (3675)
      next := (3675)
      square := (66735713816478640092455521155000000000000)
      linear := (-1611527190908815173778050049381500000000000)
      constant := (9347707592591664385000737561636286073485943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46850948099995593639/20000000000000000000)
  centralHi := (58563685124994492049/25000000000000000000)
  directionLo := (239519549332557937093/100000000000000000000)
  directionHi := (119759774666278968547/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree024.table
  base := (-350718818364647544686277429909518051763/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-24455771298097096189549022150915970500000000000)
      constant := (147870771968716847666362187891667500056528635624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree024.table
  base := (-5617345541715406750064026378369576954039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (4900)
      previous := (2450)
      next := (2450)
      square := (44490475877652426728303680770000000000000)
      linear := (-1120960530572941229567399127061000000000000)
      constant := (6785514183484341086176131245963890729252089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239519549332557937093/100000000000000000000)
  centralHi := (119759774666278968547/50000000000000000000)
  directionLo := (122335548368239324001/50000000000000000000)
  directionHi := (244671096736478648003/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree025.table
  base := (-5979394490127371314320111863426217424743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-50945259450602098929397456225989631000000000000)
      constant := (321078648772897050398212411414284315436820249833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree025.table
  base := (-23938104146594139927080555071426789241/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29400000000000000000000000000000000000000
      center := (294)
      previous := (147)
      next := (147)
      square := (2669428552659145603698220846200000000000)
      linear := (-70054176032400340596965893272060000000000)
      constant := (442013956700017662409378291234001309907865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122335548368239324001/50000000000000000000)
  centralHi := (244671096736478648003/100000000000000000000)
  directionLo := (49943278484292930809/20000000000000000000)
  directionHi := (124858196210732327023/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree026.table
  base := (-785770745144974868602544013489129462447/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-26489488152505002739848434075073660500000000000)
      constant := (173805349461248410856308395878545757346367108228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree026.table
  base := (-629066444859060422412716459540499110561/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 147000000000000000000000000000000000000000
      center := (1470)
      previous := (735)
      next := (735)
      square := (13347142763295728018491104231000000000000)
      linear := (-364253601152121037099439194602300000000000)
      constant := (2392706912998238707063456397233346630747533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49943278484292930809/20000000000000000000)
  centralHi := (124858196210732327023/50000000000000000000)
  directionLo := (254661751564208336051/100000000000000000000)
  directionHi := (63665437891052084013/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree027.table
  base := (-6536475954875053610020810548866174748949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-55012693159417912029996280074305011000000000000)
      constant := (375327719307928820775755785675694556418766777819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree027.table
  base := (-6540413695717545999300458073354085230897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (4900)
      previous := (2450)
      next := (2450)
      square := (44490475877652426728303680770000000000000)
      linear := (-1260787740474134570713496409481000000000000)
      constant := (8611657485475224391755678300192649823686047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254661751564208336051/100000000000000000000)
  centralHi := (63665437891052084013/25000000000000000000)
  directionLo := (259512887494070714179/100000000000000000000)
  directionHi := (12975644374703535709/5000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree028.table
  base := (-6734252157268337264042359720943623068431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4368100)
      previous := (2184050)
      next := (2184050)
      square := (39660989322688482692225164892130000000000000)
      linear := (-1164212449261751399597871265274749000000000000)
      constant := (8249414351670350676542963823346123600747865489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree028.table
  base := (-1684423586664913053836653729558110767911/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (1361953343193441634539908595000000000000)
      linear := (-40022351340036704625373331743500000000000)
      constant := (283916647864715189019204160980651335392534) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259512887494070714179/100000000000000000000)
  centralHi := (12975644374703535709/5000000000000000000)
  directionLo := (26427498905736396089/10000000000000000000)
  directionHi := (264274989057363960891/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree029.table
  base := (-275312204506510939510270733061444916261/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 856147600000000000000000000000000000000000000
      center := (8561476)
      previous := (4280738)
      next := (4280738)
      square := (77735539072469426076761323188574800000000000)
      linear := (-2363205074729349005223804156904815640000000000)
      constant := (17371374596312382766002386642244825766027359691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree029.table
  base := (-6885810289126257364196260572333494600259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-4062017641224790394432683793283000000000000)
      constant := (29893160561438360946165680658893976293761927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26427498905736396089/10000000000000000000)
  centralHi := (264274989057363960891/100000000000000000000)
  directionLo := (134476392823266082781/50000000000000000000)
  directionHi := (268952785646532165563/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree030.table
  base := (-6984925397975771382447378135257004302947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-61113843722641631680894515846778081000000000000)
      constant := (465510931471489840773414376872090805957105632557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree030.table
  base := (-6987545930844472158330372687262475805893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (4900)
      previous := (2450)
      next := (2450)
      square := (44490475877652426728303680770000000000000)
      linear := (-1400614950375327911859593691901000000000000)
      constant := (10680850120192868389127783278054138685511243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134476392823266082781/50000000000000000000)
  centralHi := (268952785646532165563/100000000000000000000)
  directionLo := (5471012044321932057/2000000000000000000)
  directionHi := (273550602216096602851/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree031.table
  base := (-3521482697031947764349829076770372229959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-31573780288524769115596963885467885500000000000)
      constant := (248947983979913206872943110040018693160534885129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree031.table
  base := (-7045247979793321130858893871560713454351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-4341672061027177076724878358123000000000000)
      constant := (34271655922089904581167853738453575122210403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5471012044321932057/2000000000000000000)
  centralHi := (273550602216096602851/100000000000000000000)
  directionLo := (69518101526935393233/25000000000000000000)
  directionHi := (278072406107741572933/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree032.table
  base := (-7058908146189917551071804430479061689073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-65181277431457444781493339695093461000000000000)
      constant := (531435229924213254828191194160561993211620512063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree032.table
  base := (-7060894299784681801410962391350238983411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-4481499270928370417870975640543000000000000)
      constant := (36580186499991913192133709046647514869438583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69518101526935393233/25000000000000000000)
  centralHi := (278072406107741572933/100000000000000000000)
  directionLo := (282521847127453826617/100000000000000000000)
  directionHi := (141260923563726913309/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree033.table
  base := (-3517212688789748835451566021945876841599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88445000000000000000000000000000000000000000
      center := (884450)
      previous := (442225)
      next := (442225)
      square := (8030530895916263024458814378985000000000000)
      linear := (-277747910272170873271870874459715500000000000)
      constant := (2339360079587113970570419382809365884548955289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree033.table
  base := (-879518988622055795174988912500767687519/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (2450)
      previous := (1225)
      next := (1225)
      square := (22245237938826213364151840385000000000000)
      linear := (-770221080138260626502845487160500000000000)
      constant := (6494649507102570141357192633316349533246276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282521847127453826617/100000000000000000000)
  centralHi := (141260923563726913309/50000000000000000000)
  directionLo := (286902292026515583239/100000000000000000000)
  directionHi := (7172557300662889581/2500000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree034.table
  base := (-1742731594373908919184153821656522847971/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-34624355570136628941046081771704420500000000000)
      constant := (300981339784190417150516586086871909196822317402) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree034.table
  base := (-6972425845797277291986908145009136750207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-4761153690730757100163170205383000000000000)
      constant := (41434581009311414164465502368725656897719571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286902292026515583239/100000000000000000000)
  centralHi := (7172557300662889581/2500000000000000000)
  directionLo := (72804213578193597743/25000000000000000000)
  directionHi := (291216854312774390973/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree035.table
  base := (-1717399801428126849934189451029698832969/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (2184050)
      previous := (1092025)
      next := (1092025)
      square := (19830494661344241346112582446065000000000000)
      linear := (-727371714231440453391750770077209500000000000)
      constant := (6519850081253063491301964298562388450554162222) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree035.table
  base := (-6870900346630296445764904111725928054677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (300)
      previous := (150)
      next := (150)
      square := (2723906686386883269079817190000000000000)
      linear := (-100020018380243886557331989547000000000000)
      constant := (897552333006766820995297651609822215835969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72804213578193597743/25000000000000000000)
  centralHi := (291216854312774390973/100000000000000000000)
  directionLo := (59093684028527888553/20000000000000000000)
  directionHi := (147734210071319721383/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree036.table
  base := (-1682861356060829418888131439636003688433/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-36658072424544535491345493695862110500000000000)
      constant := (338535440365527551598423167920205385842784696446) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree036.table
  base := (-336628677402088157449791717258626292467/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49000000000000000000000000000000000000000
      center := (490)
      previous := (245)
      next := (245)
      square := (4449047587765242672830368077000000000000)
      linear := (-168026937017771459415178825674100000000000)
      constant := (1553473341353355364003163300468254623338234) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59093684028527888553/20000000000000000000)
  centralHi := (147734210071319721383/50000000000000000000)
  directionLo := (149829835452878792427/50000000000000000000)
  directionHi := (59931934181151516971/20000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree037.table
  base := (-6557309374747250191884447492097993375477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-75349861703496977532990399315881911000000000000)
      constant := (716337590670432752118334783770375697016923668987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree037.table
  base := (-204946460420418177005163050967536139241/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (7350)
      previous := (3675)
      next := (3675)
      square := (66735713816478640092455521155000000000000)
      linear := (-2590317660217168561800731026321500000000000)
      constant := (24653432555227841855928036681369855000505168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149829835452878792427/50000000000000000000)
  centralHi := (59931934181151516971/20000000000000000000)
  directionLo := (151896551502253151023/50000000000000000000)
  directionHi := (303793103004506302047/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree038.table
  base := (-6347902858990127465956403004707402239831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (592900)
      previous := (296450)
      next := (296450)
      square := (5383347581195943634124745373170000000000000)
      linear := (-214358943373697739842908064376841000000000000)
      constant := (2096243529813017886805235141931982812120042001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree038.table
  base := (-6348748982728502410093252695209885013329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-5320462530335530464747559335063000000000000)
      constant := (52087954692156730092486538762218146903040637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151896551502253151023/50000000000000000000)
  centralHi := (303793103004506302047/100000000000000000000)
  directionLo := (9620970163836079389/3125000000000000000)
  directionHi := (307871045242754540449/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree039.table
  base := (-1525956486138300455785248402594063069611/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-39708647706156395316794611582098645500000000000)
      constant := (399144283570603200396753106969883807643519547082) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree039.table
  base := (-610455794765815383835970447876910740899/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49000000000000000000000000000000000000000
      center := (490)
      previous := (245)
      next := (245)
      square := (4449047587765242672830368077000000000000)
      linear := (-182009658007890793529788553916100000000000)
      constant := (1831579371029683962653468992205931373695949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9620970163836079389/3125000000000000000)
  centralHi := (307871045242754540449/100000000000000000000)
  directionLo := (31189567416786313989/10000000000000000000)
  directionHi := (311895674167863139891/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree040.table
  base := (-1456396126080101552587699382413689971767/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-40725506133360348591944317544177490500000000000)
      constant := (420485233275957436205566719372000155617638075954) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree040.table
  base := (-5826217362428590384619778005252020815699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-5600116950137917147039753899903000000000000)
      constant := (57885070377731670671167351236147952940092247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31189567416786313989/10000000000000000000)
  centralHi := (311895674167863139891/100000000000000000000)
  directionLo := (12634761106115808949/4000000000000000000)
  directionHi := (157934513826447611863/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree041.table
  base := (-5513605002601503653384356742009219727523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-83484729121128603734188047012512671000000000000)
      constant := (884788699703636648811806161152095589381021324013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree041.table
  base := (-2757075901146259754395402406626192217683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (7350)
      previous := (3675)
      next := (3675)
      square := (66735713816478640092455521155000000000000)
      linear := (-2869972080019555244092925591161500000000000)
      constant := (30450480010059018735284267717977449744000599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12634761106115808949/4000000000000000000)
  centralHi := (157934513826447611863/50000000000000000000)
  directionLo := (159896508479817285781/50000000000000000000)
  directionHi := (319793016959634571563/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree042.table
  base := (-5168246960168615589544116359140952872611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4368100)
      previous := (2184050)
      next := (2184050)
      square := (39660989322688482692225164892130000000000000)
      linear := (-1745274407664010413969131815034089000000000000)
      constant := (18974336675290943371569118041280947037571478909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree042.table
  base := (-5168719122943349513165522653874729172871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (100)
      previous := (50)
      next := (50)
      square := (907968895462294423026605730000000000000)
      linear := (-39998444693471454621305771869000000000000)
      constant := (435340118729678151410684285144125270827129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159896508479817285781/50000000000000000000)
  centralHi := (319793016959634571563/100000000000000000000)
  directionLo := (161834718742537413773/50000000000000000000)
  directionHi := (323669437485074827547/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree043.table
  base := (-4789813462590128477308953454196401866821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-87552162829944416834786870860828051000000000000)
      constant := (975831209993818679840627331713839379532714203051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree043.table
  base := (-479022094509067711095498322351061845251/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 147000000000000000000000000000000000000000
      center := (1470)
      previous := (735)
      next := (735)
      square := (13347142763295728018491104231000000000000)
      linear := (-601959857984149717047804574716300000000000)
      constant := (6716713833892131231473149007747293908748103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161834718742537413773/50000000000000000000)
  centralHi := (323669437485074827547/100000000000000000000)
  directionLo := (327499978362845696071/100000000000000000000)
  directionHi := (40937497295355712009/12500000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree044.table
  base := (-875712003805761456221178739121108656933/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35378000000000000000000000000000000000000000
      center := (353780)
      previous := (176890)
      next := (176890)
      square := (3212212358366505209783525751594000000000000)
      linear := (-148075834189012104768737657495844200000000000)
      constant := (1690998828980880685336995199541161508967512163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree044.table
  base := (-2189455745719207923385906667486632136343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (7350)
      previous := (3675)
      next := (3675)
      square := (66735713816478640092455521155000000000000)
      linear := (-3079712894871345255812071514791500000000000)
      constant := (35208672653178217175796589889165465075957579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327499978362845696071/100000000000000000000)
  centralHi := (40937497295355712009/12500000000000000000)
  directionLo := (331286231065258787161/100000000000000000000)
  directionHi := (165643115532629393581/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree045.table
  base := (-3934702030444778534653288042625309314189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-91619596538760229935385694709143431000000000000)
      constant := (1071411280670561004502802862924142604328498604259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree045.table
  base := (-61484453671612098661863240741717417751/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (2450)
      previous := (1225)
      next := (1225)
      square := (22245237938826213364151840385000000000000)
      linear := (-1049875499940647308795040052000500000000000)
      constant := (12290931142906258817445900593189487088966432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331286231065258787161/100000000000000000000)
  centralHi := (165643115532629393581/50000000000000000000)
  directionLo := (335029697130244968183/100000000000000000000)
  directionHi := (41878712141280621023/12500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree046.table
  base := (-3458421085492812622453783006200092158127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-93653313393168136485685106633301121000000000000)
      constant := (1120901788738475827229282088309075515947601871137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree046.table
  base := (-3458682176858788260128424891003463427817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-6439080209545077193916337594423000000000000)
      constant := (77151836443797994119255723920740490876110901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335029697130244968183/100000000000000000000)
  centralHi := (41878712141280621023/12500000000000000000)
  directionLo := (10585368597487345023/3125000000000000000)
  directionHi := (338731795119595040737/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree047.table
  base := (-1474935134067801386313466832669458365327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-47843515123788021517992259278729405500000000000)
      constant := (585762744040504568533171373946148990068063414337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree047.table
  base := (-29500951376579391818313615505214148743/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29400000000000000000000000000000000000000
      center := (294)
      previous := (147)
      next := (147)
      square := (2669428552659145603698220846200000000000)
      linear := (-131578148388925410701248697536860000000000)
      constant := (1612721433780212676303291890913887040269558) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10585368597487345023/3125000000000000000)
  centralHi := (338731795119595040737/100000000000000000000)
  directionLo := (68478773379990663453/20000000000000000000)
  directionHi := (171196933449976658633/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree048.table
  base := (-481835726421456215300722411134671399717/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4280738000000000000000000000000000000000000000
      center := (42807380)
      previous := (21403690)
      next := (21403690)
      square := (388677695362347130383806615942874000000000000)
      linear := (-19544149420396789917256786096323300200000000000)
      constant := (244656420495109812688759014885155456110859124427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree048.table
  base := (-602343054314298319092237939966962143713/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (2450)
      previous := (1225)
      next := (1225)
      square := (22245237938826213364151840385000000000000)
      linear := (-1119789104891243979368088693210500000000000)
      constant := (14033045622165602793576263993507237709916126) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68478773379990663453/20000000000000000000)
  centralHi := (171196933449976658633/50000000000000000000)
  directionLo := (69203436665085523781/20000000000000000000)
  directionHi := (173008591662713809453/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree049.table
  base := (-918227486504538671145652742046017344341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (2184050)
      previous := (1092025)
      next := (1092025)
      square := (19830494661344241346112582446065000000000000)
      linear := (-1017902693432569960577381044956879500000000000)
      constant := (13022157133258810180798732821530158416381840779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree049.table
  base := (-1836621553809928563427175941740893440319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (300)
      previous := (150)
      next := (150)
      square := (2723906686386883269079817190000000000000)
      linear := (-139970649780584841170502641667000000000000)
      constant := (1792620952641599926311037817237777319679043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69203436665085523781/20000000000000000000)
  centralHi := (173008591662713809453/50000000000000000000)
  directionLo := (349602949390050515663/100000000000000000000)
  directionHi := (21850184336878157229/6250000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree050.table
  base := (-615895504144813370728515488461384256667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-50894090405399881343441377164965940500000000000)
      constant := (665096590761634161038233643189604232939941909877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree050.table
  base := (-615967146019167738253434974372401547173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (7350)
      previous := (3675)
      next := (3675)
      square := (66735713816478640092455521155000000000000)
      linear := (-3499194524574925279250363362051500000000000)
      constant := (45778258565035405352394889463092256972565569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349602949390050515663/100000000000000000000)
  centralHi := (21850184336878157229/6250000000000000000)
  directionLo := (353152308909317283271/100000000000000000000)
  directionHi := (44144038613664660409/12500000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree051.table
  base := (-595264058055722735619059324710208661947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-103821897665207669237182166254089571000000000000)
      constant := (1385347284373704179103719047399848841396437161557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree051.table
  base := (-59538725364919693537566067297103433319/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49000000000000000000000000000000000000000
      center := (490)
      previous := (245)
      next := (245)
      square := (4449047587765242672830368077000000000000)
      linear := (-237940541968368129988227466884100000000000)
      constant := (3178417793069998753963284015083541931767369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353152308909317283271/100000000000000000000)
  centralHi := (44144038613664660409/12500000000000000000)
  directionLo := (44583293597795249523/12500000000000000000)
  directionHi := (71333269756472399237/20000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree052.table
  base := (36530347465327360741644355404998129203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-52927807259807787893740789089123630500000000000)
      constant := (720816784047753946264213011666200641440804095907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree052.table
  base := (36477405944331963233833148990727936469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (7350)
      previous := (3675)
      next := (3675)
      square := (66735713816478640092455521155000000000000)
      linear := (-3639021734476118620396460644471500000000000)
      constant := (49613233573676967565471378071119637006660943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44583293597795249523/12500000000000000000)
  centralHi := (71333269756472399237/20000000000000000000)
  directionLo := (22509131429986948829/6250000000000000000)
  directionHi := (72029220575958236253/20000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree053.table
  base := (773128300012919296702988142642777139063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-107889331374023482337780990102404951000000000000)
      constant := (1499051915073997575317296649452476141262359134247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree053.table
  base := (773037330261948193923571310043060056021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-7417870678853430581939018571363000000000000)
      constant := (103178309173408673300402853666235329828235087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22509131429986948829/6250000000000000000)
  centralHi := (72029220575958236253/20000000000000000000)
  directionLo := (363592555596591898889/100000000000000000000)
  directionHi := (36359255559659189889/10000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree054.table
  base := (752446216235467574532383254064914687819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-54961524114215694444040201013281320500000000000)
      constant := (778801113078589157520259261407222961885452465211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree054.table
  base := (150481430334468436582540072095157666653/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49000000000000000000000000000000000000000
      center := (490)
      previous := (245)
      next := (245)
      square := (4449047587765242672830368077000000000000)
      linear := (-251923262958487464102837195126100000000000)
      constant := (3573601770284655310553577164636062725665997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363592555596591898889/100000000000000000000)
  centralHi := (36359255559659189889/10000000000000000000)
  directionLo := (367006645104717972003/100000000000000000000)
  directionHi := (91751661276179493001/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree055.table
  base := (2268314039476754650261811029560477641793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (1768900)
      previous := (884450)
      next := (884450)
      square := (16061061791832526048917628757970000000000000)
      linear := (-925262521345779301143634826039011000000000000)
      constant := (13365986923616428183973886106281775289005676377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree055.table
  base := (1134123480748817349815409928574602907919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (7350)
      previous := (3675)
      next := (3675)
      square := (66735713816478640092455521155000000000000)
      linear := (-3848762549327908632115606568101500000000000)
      constant := (55657846626804962615701208381882966627464093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367006645104717972003/100000000000000000000)
  centralHi := (91751661276179493001/25000000000000000000)
  directionLo := (370389266335810608019/100000000000000000000)
  directionHi := (18519463316790530401/5000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree056.table
  base := (1531680099299213658028291681728592015683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (2184050)
      previous := (1092025)
      next := (1092025)
      square := (19830494661344241346112582446065000000000000)
      linear := (-1163168183033134714170196182396714500000000000)
      constant := (17123453259276258260737395121252368627837049123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree056.table
  base := (765825656912573762042656483412639849149/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (1361953343193441634539908595000000000000)
      linear := (-79972982740377659238543983863500000000000)
      constant := (1178583926582552111583207003376475839094894) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370389266335810608019/100000000000000000000)
  centralHi := (18519463316790530401/5000000000000000000)
  directionLo := (1868706368604626997/500000000000000000)
  directionHi := (373741273720925399401/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree057.table
  base := (389000315548769840497737505390368980643/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5929000000000000000000000000000000000000000
      center := (59290)
      previous := (29645)
      next := (29645)
      square := (538334758119594363412474537317000000000000)
      linear := (-32139667255306124249024553406935100000000000)
      constant := (482006695763736341623834618483733197686232347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree057.table
  base := (243122109992829699812860541004462696881/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (2450)
      previous := (1225)
      next := (1225)
      square := (22245237938826213364151840385000000000000)
      linear := (-1329529919743033991087234616840500000000000)
      constant := (19960773952386391344390063874532249377177352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1868706368604626997/500000000000000000)
  centralHi := (373741273720925399401/100000000000000000000)
  directionLo := (188531741855515751589/50000000000000000000)
  directionHi := (377063483711031503179/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree058.table
  base := (4748219512624665230397716753129047197959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-118057915646063015089278049723193401000000000000)
      constant := (1803121624572306184796702961819309808622048306871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree058.table
  base := (1187044286118650638297445555013994078153/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (7350)
      previous := (3675)
      next := (3675)
      square := (66735713816478640092455521155000000000000)
      linear := (-4058503364179698643834752491731500000000000)
      constant := (62052973284438318326898788519711114258976982) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188531741855515751589/50000000000000000000)
  centralHi := (377063483711031503179/100000000000000000000)
  directionLo := (380356677099349679493/100000000000000000000)
  directionHi := (190178338549674839747/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree059.table
  base := (5637989545407606515219505321605131955947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-120091632500470921639577461647351091000000000000)
      constant := (1867330735786801222588103499243182348679418324443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree059.table
  base := (1409488303931357058252067086758515650039/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (7350)
      previous := (3675)
      next := (3675)
      square := (66735713816478640092455521155000000000000)
      linear := (-4128416969130295314407801132941500000000000)
      constant := (64262565246304061955809925580315503601111466) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380356677099349679493/100000000000000000000)
  centralHi := (190178338549674839747/50000000000000000000)
  directionLo := (191810800582122195901/50000000000000000000)
  directionHi := (383621601164244391803/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree060.table
  base := (3279648312799146177489804215163374038853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-61062674677439414094938436785754390500000000000)
      constant := (966335734880003837366929367458996970728165756757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree060.table
  base := (409954092669242153698673467771625138253/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (2450)
      previous := (1225)
      next := (1225)
      square := (22245237938826213364151840385000000000000)
      linear := (-1399443524693630661660283258050500000000000)
      constant := (22170365510224352967757780872096477054195176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191810800582122195901/50000000000000000000)
  centralHi := (383621601164244391803/100000000000000000000)
  directionLo := (48357371456166430717/12500000000000000000)
  directionHi := (386858971649331445737/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree061.table
  base := (300485069410836395148846673484018111449/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 856147600000000000000000000000000000000000000
      center := (8561476)
      previous := (4280738)
      next := (4280738)
      square := (77735539072469426076761323188574800000000000)
      linear := (-4966362648371469389607051419826658840000000000)
      constant := (79965751859535667482606864279375610001183984681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree061.table
  base := (7512100046069194952726130506142500569131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-8536488358062977311107796830723000000000000)
      constant := (137597132231885764635568728805765947583662257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48357371456166430717/12500000000000000000)
  centralHi := (386858971649331445737/100000000000000000000)
  directionLo := (390069474595664648351/100000000000000000000)
  directionHi := (12189671081114520261/3125000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree062.table
  base := (67971744456464126018391225588675074607/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 856147600000000000000000000000000000000000000
      center := (8561476)
      previous := (4280738)
      next := (4280738)
      square := (77735539072469426076761323188574800000000000)
      linear := (-5047711322547785651619027896792966440000000000)
      constant := (82669907627137052890415236892811199883807549915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree062.table
  base := (1699289038155554000739527739347560092979/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294000000000000000000000000000000000000000
      center := (2940)
      previous := (1470)
      next := (1470)
      square := (26694285526591456036982208462000000000000)
      linear := (-1735263113592834130450778822628600000000000)
      constant := (28449989256423483260264587151397291333667913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390069474595664648351/100000000000000000000)
  centralHi := (12189671081114520261/3125000000000000000)
  directionLo := (196626884019643601779/50000000000000000000)
  directionHi := (393253768039287203559/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree063.table
  base := (9512310628716968068630998776523027464083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4368100)
      previous := (2184050)
      next := (2184050)
      square := (39660989322688482692225164892130000000000000)
      linear := (-2616867345267398935526022639673099000000000000)
      constant := (43581288387902780798029956645605754362658609523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree063.table
  base := (4756145521432526227869245459874098232661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (50)
      previous := (25)
      next := (25)
      square := (453984447731147211513302865000000000000)
      linear := (-29986880196820965963945548964500000000000)
      constant := (499934128437305089700085541303374098232661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196626884019643601779/50000000000000000000)
  centralHi := (393253768039287203559/100000000000000000000)
  directionLo := (79282496717209188267/20000000000000000000)
  directionHi := (49551560448255742667/12500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree064.table
  base := (10559646051920277145184049997965782093927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-130260216772510454391074521268139541000000000000)
      constant := (2205350099499301686830118128455563447054596439063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree064.table
  base := (10559629280108595825133760948499789485941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-8955969987766557334546088677983000000000000)
      constant := (151789193443869905213969274809061469054433327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79282496717209188267/20000000000000000000)
  centralHi := (49551560448255742667/12500000000000000000)
  directionLo := (49943278484292930809/12500000000000000000)
  directionHi := (399546227874343446473/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree065.table
  base := (11638467246758196060030222954376106167733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-132293933626918360941373933192297231000000000000)
      constant := (2276348581001003260330791924847943996982124513477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree065.table
  base := (5819226444089832575817031980808307469449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (7350)
      previous := (3675)
      next := (3675)
      square := (66735713816478640092455521155000000000000)
      linear := (-4547898598833875337846092980201500000000000)
      constant := (78337812150458859394299326592926321198009003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49943278484292930809/12500000000000000000)
  centralHi := (399546227874343446473/100000000000000000000)
  directionLo := (201327791967711463073/50000000000000000000)
  directionHi := (402655583935422926147/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree066.table
  base := (3187192061194492687000562575668951082731/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88445000000000000000000000000000000000000000
      center := (884450)
      previous := (442225)
      next := (442225)
      square := (8030530895916263024458814378985000000000000)
      linear := (-555072935873249039221790682299400500000000000)
      constant := (9704456870816734408428848206512341651404857318) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree066.table
  base := (12748755955110956423747962180635647854477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (4900)
      previous := (2450)
      next := (2450)
      square := (44490475877652426728303680770000000000000)
      linear := (-3078541469189648005612761080941000000000000)
      constant := (53879975154217314468674680973377146744869373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201327791967711463073/50000000000000000000)
  centralHi := (402655583935422926147/100000000000000000000)
  directionLo := (202870556229912313033/50000000000000000000)
  directionHi := (405741112459824626067/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree067.table
  base := (13890544014510538025147039457855440526981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-136361367335734174041972757040612611000000000000)
      constant := (2421740033940040679059111655016607433385293795989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree067.table
  base := (3472633374515664266660878169933182483233/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (7350)
      previous := (3675)
      next := (3675)
      square := (66735713816478640092455521155000000000000)
      linear := (-4687725808735068678992190262621500000000000)
      constant := (83341048098297563308872574200900855650070502) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202870556229912313033/50000000000000000000)
  centralHi := (405741112459824626067/100000000000000000000)
  directionLo := (408803352977804832987/100000000000000000000)
  directionHi := (102200838244451208247/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree068.table
  base := (15063790314385019839966285978600933503429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-138395084190142080592272168964770301000000000000)
      constant := (2496132985529649298304575717591055279441800825301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree068.table
  base := (15063781317311360974413691759291859457049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-9515278827371330699130477807663000000000000)
      constant := (171802135885387927726193637147019903340186203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408803352977804832987/100000000000000000000)
  centralHi := (102200838244451208247/25000000000000000000)
  directionLo := (41184282496075530003/10000000000000000000)
  directionHi := (411842824960755300031/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree069.table
  base := (16268503568731867386426759212852217650759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-140428801044549987142571580888927991000000000000)
      constant := (2571657409853223328067752913841811067240937390071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree069.table
  base := (8134247936591965483081460902429048862973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (2450)
      previous := (1225)
      next := (1225)
      square := (22245237938826213364151840385000000000000)
      linear := (-1609184339545420673379429181680500000000000)
      constant := (29500007334783065927629643207743523394285677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41184282496075530003/10000000000000000000)
  centralHi := (411842824960755300031/100000000000000000000)
  directionLo := (51857503606248814911/12500000000000000000)
  directionHi := (414860028849990519289/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree070.table
  base := (3500936152650071374916149971923950073761/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87362000000000000000000000000000000000000000
      center := (873620)
      previous := (436810)
      next := (436810)
      square := (7932197864537696538445032978426000000000000)
      linear := (-581479664893705688542330582910553800000000000)
      constant := (10809442042689987520290108796571531063171954241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree070.table
  base := (140037393458645174120407660958168053657/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1200000000000000000000000000000000000000
      center := (12)
      previous := (6)
      next := (6)
      square := (108956267455475330763192687600000000000)
      linear := (-7995863875243850923610344793880000000000)
      constant := (148796587859570711229226366249972520804855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51857503606248814911/12500000000000000000)
  centralHi := (414860028849990519289/100000000000000000000)
  directionLo := (208927723509336239533/50000000000000000000)
  directionHi := (417855447018672479067/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree071.table
  base := (4693079839221263604516075244243360907649/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-72248117376682900121585202368621685500000000000)
      constant := (1363050325954161931771312002694927724285087564962) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree071.table
  base := (18772313730298583035149206425883601599697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-9934760457074910722568769654923000000000000)
      constant := (187629463873590524771885452237897889435155459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208927723509336239533/50000000000000000000)
  centralHi := (417855447018672479067/100000000000000000000)
  directionLo := (84165908934421718241/20000000000000000000)
  directionHi := (210414772336054295603/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree072.table
  base := (10035708603767739559505126601147222193957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-73264975803886853396734908330700530500000000000)
      constant := (1402509729808084313541753965256746464820057550133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree072.table
  base := (20071412397843730065049891955313550173629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (4900)
      previous := (2450)
      next := (2450)
      square := (44490475877652426728303680770000000000000)
      linear := (-3358195888992034687904955645781000000000000)
      constant := (64353658311339578895483458960042363958507821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84165908934421718241/20000000000000000000)
  centralHi := (210414772336054295603/50000000000000000000)
  directionLo := (211891385345590369963/50000000000000000000)
  directionHi := (423782770691180739927/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree073.table
  base := (21401972509427519262453209146541623024241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-148563668462181613343769228585558751000000000000)
      constant := (2885069719717558303376479657886752980130771684929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree073.table
  base := (53504920997057227814782554858575899929/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29400000000000000000000000000000000000000
      center := (294)
      previous := (147)
      next := (147)
      square := (2669428552659145603698220846200000000000)
      linear := (-204288297537545948097219284395260000000000)
      constant := (3971407060933914141607151874400065258316504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211891385345590369963/50000000000000000000)
  centralHi := (423782770691180739927/100000000000000000000)
  directionLo := (213357779211617636027/50000000000000000000)
  directionHi := (85343111684647054411/20000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree074.table
  base := (711374491884875448510097768278892860587/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-75298692658294759947034320254858220500000000000)
      constant := (1483125714477163270247863125791870589629947785648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree074.table
  base := (11381990113922829206873583975897718253417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (7350)
      previous := (3675)
      next := (3675)
      square := (66735713816478640092455521155000000000000)
      linear := (-5177121043389245373003530751091500000000000)
      constant := (102078798995164523003210181388537964583252299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213357779211617636027/50000000000000000000)
  centralHi := (85343111684647054411/20000000000000000000)
  directionLo := (21481416321218973103/5000000000000000000)
  directionHi := (429628326424379462061/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree075.table
  base := (4831489923395053649276085250471962878337/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4280738000000000000000000000000000000000000000
      center := (42807380)
      previous := (21403690)
      next := (21403690)
      square := (388677695362347130383806615942874000000000000)
      linear := (-30526220434199485288873610486774826200000000000)
      constant := (609712916915979367682995702546043214713943286353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree075.table
  base := (24157446616152723673494991308977455877471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (4900)
      previous := (2450)
      next := (2450)
      square := (44490475877652426728303680770000000000000)
      linear := (-3498023098893228029051052928201000000000000)
      constant := (69940903192803711717048418422214895337996079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21481416321218973103/5000000000000000000)
  centralHi := (429628326424379462061/100000000000000000000)
  directionLo := (432521479156784523631/100000000000000000000)
  directionHi := (27032592447299032727/6250000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree076.table
  base := (25582369057676504725926345722125886724417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (592900)
      previous := (296450)
      next := (296450)
      square := (5383347581195943634124745373170000000000000)
      linear := (-428434401732424745137583003761861000000000000)
      constant := (8675925718224294897805530201473330382389068393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree076.table
  base := (25582366494427797978422757365725849240531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-10633896506580877428299256067023000000000000)
      constant := (215565687653752480042302412195269699838358057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432521479156784523631/100000000000000000000)
  centralHi := (27032592447299032727/6250000000000000000)
  directionLo := (435395407644284215989/100000000000000000000)
  directionHi := (43539540764428421599/10000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree077.table
  base := (1689921321909718558166729929265252689723/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (18050)
      previous := (9025)
      next := (9025)
      square := (163888385630944143356302334265000000000000)
      linear := (-13214583899461396487178856154679500000000000)
      constant := (271258663020730433141629364817449549767920024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree077.table
  base := (6759684740363389764774369765254493982263/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (1361953343193441634539908595000000000000)
      linear := (-109935956290633375198421972953500000000000)
      constant := (2259046245753817697002910045561026963893578) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435395407644284215989/100000000000000000000)
  centralHi := (43539540764428421599/10000000000000000000)
  directionLo := (109562622522319416997/25000000000000000000)
  directionHi := (438250490089277667989/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree078.table
  base := (7131641281736441306751424502403271169459/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-79366126367110573047633144103173600500000000000)
      constant := (1651146354198609994162513126691239330719407580742) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree078.table
  base := (1141062530307730630219401592591432703857/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19600000000000000000000000000000000000000
      center := (196)
      previous := (98)
      next := (98)
      square := (1779619035106097069132147230800000000000)
      linear := (-145514012351776854807886008424840000000000)
      constant := (3030469903428322626567580759180100202488993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109562622522319416997/25000000000000000000)
  centralHi := (438250490089277667989/100000000000000000000)
  directionLo := (6891985819588935137/1562500000000000000)
  directionHi := (441087092453691848769/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree079.table
  base := (30045840338897876315293325211953342712023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-160765969588629052645565700130504891000000000000)
      constant := (3389131629784315113900419822312241728187189956487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree079.table
  base := (7511459685755998511625089884499444603143/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (7350)
      previous := (3675)
      next := (3675)
      square := (66735713816478640092455521155000000000000)
      linear := (-5526689068142228725868773957141500000000000)
      constant := (116630909789702299135026511421381336713324042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6891985819588935137/1562500000000000000)
  centralHi := (441087092453691848769/100000000000000000000)
  directionLo := (110976392251632547909/25000000000000000000)
  directionHi := (443905569006530191637/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree080.table
  base := (7899141560056932970342452052886520598981/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-81399843221518479597932556027331290500000000000)
      constant := (1738550994546035670297519889816331278415840727978) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree080.table
  base := (3949570609746135729676510544303598504367/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (7350)
      previous := (3675)
      next := (3675)
      square := (66735713816478640092455521155000000000000)
      linear := (-5596602673092825396441822598351500000000000)
      constant := (119658131235706134699406536578970515920567796) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110976392251632547909/25000000000000000000)
  centralHi := (443905569006530191637/100000000000000000000)
  directionLo := (111676565710081656061/25000000000000000000)
  directionHi := (89341252568065324849/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree081.table
  base := (16589371185269942060628822659331620524613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-82416701648722432873082261989410135500000000000)
      constant := (1783101892667536262094067302014799791790645402197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree081.table
  base := (33178741207879923976919831277874770799711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (4900)
      previous := (2450)
      next := (2450)
      square := (44490475877652426728303680770000000000000)
      linear := (-3777677518695614711343247493041000000000000)
      constant := (81816190455437954552535850528356863769185839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111676565710081656061/25000000000000000000)
  centralHi := (89341252568065324849/20000000000000000000)
  directionLo := (224744753179318188641/50000000000000000000)
  directionHi := (449489506358636377283/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree082.table
  base := (434904604271985911285367111152210966371/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2140369000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (194338847681173565191903307971437000000000000)
      linear := (-16686712015185277229646393590297796100000000000)
      constant := (365643701768269398015216275971547943771044247192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree082.table
  base := (34792367349603558538416319796075751586131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-11472859765988037475175839761543000000000000)
      constant := (251658746207785897407225187888849135483161257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224744753179318188641/50000000000000000000)
  centralHi := (449489506358636377283/100000000000000000000)
  directionLo := (56531952717065551117/12500000000000000000)
  directionHi := (452255621736524408937/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree083.table
  base := (18218721913387443404156557020508525243181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-84450418503130339423381673913567825500000000000)
      constant := (1873900842717400004266339649002633820666222073789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree083.table
  base := (9109360745061385482006175498665355593033/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (7350)
      previous := (3675)
      next := (3675)
      square := (66735713816478640092455521155000000000000)
      linear := (-5806343487944615408160968521981500000000000)
      constant := (128973393474181443425683042712932114544351702) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56531952717065551117/12500000000000000000)
  centralHi := (452255621736524408937/100000000000000000000)
  directionLo := (455004921355857300161/100000000000000000000)
  directionHi := (227502460677928650081/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree084.table
  base := (38113968549871850494406722952137129862661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4368100)
      previous := (2184050)
      next := (2184050)
      square := (39660989322688482692225164892130000000000000)
      linear := (-3488460282870787457082913464312109000000000000)
      constant := (78373424244923601405371753524139007969530895141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree084.table
  base := (38113967827698717731106911453775555552349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (100)
      previous := (50)
      next := (50)
      square := (907968895462294423026605730000000000000)
      linear := (-79949076093812409234476423989000000000000)
      constant := (1798045534340442721068560873689775555552349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455004921355857300161/100000000000000000000)
  centralHi := (227502460677928650081/50000000000000000000)
  directionLo := (228868854108531729137/50000000000000000000)
  directionHi := (18309508328682538331/4000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree085.table
  base := (39821942278658140040692386930140868878073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-172968270715076491947362171675451031000000000000)
      constant := (3933925324884659533444851888968554116379692228937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree085.table
  base := (39821941662660448913803036213659589482071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-11892341395691617498614131608803000000000000)
      constant := (270756465973124989200384869850362959653864437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228868854108531729137/50000000000000000000)
  centralHi := (18309508328682538331/4000000000000000000)
  directionLo := (460454276328898004293/100000000000000000000)
  directionHi := (230227138164449002147/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree086.table
  base := (41561364817264049016599738890397583107409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-175001987569484398497661583599608721000000000000)
      constant := (4028684295665775754594493730835931925558021893921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree086.table
  base := (41561364291904380963960316548166672863919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-12032168605592810839760228891223000000000000)
      constant := (277278104195198340347998894000018500910996093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460454276328898004293/100000000000000000000)
  centralHi := (230227138164449002147/50000000000000000000)
  directionLo := (231577455538815780353/50000000000000000000)
  directionHi := (463154911077631560707/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree087.table
  base := (8666447200121430926371352779489291544143/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4280738000000000000000000000000000000000000000
      center := (42807380)
      previous := (21403690)
      next := (21403690)
      square := (388677695362347130383806615942874000000000000)
      linear := (-35407140884778461009592199104753282200000000000)
      constant := (824914939998253566425389945189909497853045808767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree087.table
  base := (43332235552609592479130610370684060848599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (4900)
      previous := (2450)
      next := (2450)
      square := (44490475877652426728303680770000000000000)
      linear := (-4057331938498001393635442057881000000000000)
      constant := (94625869396776819331253547998210518981581351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231577455538815780353/50000000000000000000)
  centralHi := (463154911077631560707/100000000000000000000)
  directionLo := (232919944788487593449/50000000000000000000)
  directionHi := (465839889576975186899/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree088.table
  base := (22567277844778973890729899490968658686131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88445000000000000000000000000000000000000000
      center := (884450)
      previous := (442225)
      next := (442225)
      square := (8030530895916263024458814378985000000000000)
      linear := (-739956286273967816521737220859190500000000000)
      constant := (17444613791584079660201042517369238603498971259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree088.table
  base := (4513455530758096649993697461428978708261/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 147000000000000000000000000000000000000000
      center := (1470)
      previous := (735)
      next := (735)
      square := (13347142763295728018491104231000000000000)
      linear := (-1231182302539519752205242345606300000000000)
      constant := (29055497793835365994464170920336459870114367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232919944788487593449/50000000000000000000)
  centralHi := (465839889576975186899/100000000000000000000)
  directionLo := (46850948099995593639/10000000000000000000)
  directionHi := (468509480999955936391/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree089.table
  base := (23484161883432202704349875275748522999859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-90551569066354059074279909686040895500000000000)
      constant := (2159874904065525748090868017327071314924685207971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree089.table
  base := (4696832344122072822733060075907987508641/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 147000000000000000000000000000000000000000
      center := (1470)
      previous := (735)
      next := (735)
      square := (13347142763295728018491104231000000000000)
      linear := (-1245165023529639086319852073848300000000000)
      constant := (29731021342227507330518191477379174163770227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46850948099995593639/10000000000000000000)
  centralHi := (468509480999955936391/100000000000000000000)
  directionLo := (235581973446934023763/50000000000000000000)
  directionHi := (471163946893868047527/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree090.table
  base := (24416770066858183764554424013375666153259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-91568427493558012349429615648119740500000000000)
      constant := (2209517255741445142025202832327351668688784812571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree090.table
  base := (48833539856133103698147502287711908003317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (4900)
      previous := (2450)
      next := (2450)
      square := (44490475877652426728303680770000000000000)
      linear := (-4197159148399194734781539340301000000000000)
      constant := (101381104875925839767598718229287883492162533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235581973446934023763/50000000000000000000)
  centralHi := (471163946893868047527/100000000000000000000)
  directionLo := (473803541479342835587/100000000000000000000)
  directionHi := (118450885369835708897/25000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree091.table
  base := (25365102353424641445433388210871268039967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (2184050)
      previous := (1092025)
      next := (1092025)
      square := (19830494661344241346112582446065000000000000)
      linear := (-1889495631035958482134271869595889500000000000)
      constant := (46116843341231089562003610035090394859253798527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree091.table
  base := (6341275558782825543635021727841516022201/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (150)
      previous := (75)
      next := (75)
      square := (1361953343193441634539908595000000000000)
      linear := (-129911271990803852505007299013500000000000)
      constant := (3174023281048967766517124751582598192266412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473803541479342835587/100000000000000000000)
  centralHi := (118450885369835708897/25000000000000000000)
  directionLo := (14888390997953288167/3125000000000000000)
  directionHi := (95285702386901044269/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree092.table
  base := (10531663483220530643549599361305323961349/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4280738000000000000000000000000000000000000000
      center := (42807380)
      previous := (21403690)
      next := (21403690)
      square := (388677695362347130383806615942874000000000000)
      linear := (-37440857739186367559891611028910972200000000000)
      constant := (924199643170830323944918762094532663341828597781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree092.table
  base := (52658317214482077668990890577034291809611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-12871131864999970886636812585743000000000000)
      constant := (318043114157177347333690882131780040896012817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14888390997953288167/3125000000000000000)
  centralHi := (95285702386901044269/20000000000000000000)
  directionLo := (479039098665115874187/100000000000000000000)
  directionHi := (119759774666278968547/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree093.table
  base := (54617878202361797108578789920196582523203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-189238005550339744349757467068712551000000000000)
      constant := (4723677216596877580479176953435368942138605481907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree093.table
  base := (27308939015279921205568568605856676963819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (2450)
      previous := (1225)
      next := (1225)
      square := (22245237938826213364151840385000000000000)
      linear := (-2168493179150194037963818311360500000000000)
      constant := (54184968743725496800760495727183477171227131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479039098665115874187/100000000000000000000)
  centralHi := (119759774666278968547/25000000000000000000)
  directionLo := (96327107112306919627/20000000000000000000)
  directionHi := (60204441945191824767/12500000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree094.table
  base := (2830444350791137971792650909474208689799/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2140369000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (194338847681173565191903307971437000000000000)
      linear := (-19127172240474765090005687899287024100000000000)
      constant := (482748764956222581770779802815541698058352791662) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree094.table
  base := (11321777373889266842517088431110425004019/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294000000000000000000000000000000000000000
      center := (2940)
      previous := (1470)
      next := (1470)
      square := (26694285526591456036982208462000000000000)
      linear := (-2630157256960471513785801430116600000000000)
      constant := (66450875290223091113988656405617632475590793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96327107112306919627/20000000000000000000)
  centralHi := (60204441945191824767/12500000000000000000)
  directionLo := (484218050243282334923/100000000000000000000)
  directionHi := (121054512560820583731/25000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree095.table
  base := (58631343814529637997812873441278474446077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (592900)
      previous := (296450)
      next := (296450)
      square := (5383347581195943634124745373170000000000000)
      linear := (-535472130911788247784920473454371000000000000)
      constant := (13663239652798878722910755890612560074990790533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree095.table
  base := (14657835922457512344156636424986974581091/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (7350)
      previous := (3675)
      next := (3675)
      square := (66735713816478640092455521155000000000000)
      linear := (-6645306747351775455037552216501500000000000)
      constant := (169738403058695990293207771974788670526840754) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484218050243282334923/100000000000000000000)
  centralHi := (121054512560820583731/25000000000000000000)
  directionLo := (121696716072981385133/25000000000000000000)
  directionHi := (486786864291925540533/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree096.table
  base := (30342624281570781163113758996807086464557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-97669578056781732000327851420592810500000000000)
      constant := (2519251405907871640342457364342005074849057401533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree096.table
  base := (60685248456920465305108052756945004657421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (4900)
      previous := (2450)
      next := (2450)
      square := (44490475877652426728303680770000000000000)
      linear := (-4476813568201581417073733905141000000000000)
      constant := (115592367152022783010683786016546305228213629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121696716072981385133/25000000000000000000)
  centralHi := (486786864291925540533/100000000000000000000)
  directionLo := (122335548368239324001/25000000000000000000)
  directionHi := (97868438694591459201/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree097.table
  base := (62770601231893272690479514695868154590439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-197372872967971370550955114765343311000000000000)
      constant := (5145707540964561363645831671337402823172583331991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree097.table
  base := (62770601141422266808130739474083770773427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-13570267914505937592367298997843000000000000)
      constant := (354155262462838149573935538421961314303693769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122335548368239324001/25000000000000000000)
  centralHi := (97868438694591459201/20000000000000000000)
  directionLo := (491884247947303967389/100000000000000000000)
  directionHi := (49188424794730396739/10000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree098.table
  base := (64887401795718906685512749281884349436969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4368100)
      previous := (2184050)
      next := (2184050)
      square := (39660989322688482692225164892130000000000000)
      linear := (-4069522241273046471454174014071449000000000000)
      constant := (107225381674555087204152778657868857267756242889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree098.table
  base := (6488740171867081312582643241160549677671/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3000000000000000000000000000000000000000
      center := (30)
      previous := (15)
      next := (15)
      square := (272390668638688326907981719000000000000)
      linear := (-27979785968177818231659992408700000000000)
      constant := (737982222722603428612994823614081649033013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (491884247947303967389/100000000000000000000)
  centralHi := (49188424794730396739/10000000000000000000)
  directionLo := (24720661623652209829/5000000000000000000)
  directionHi := (494413232473044196581/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree099.table
  base := (6703565023351337176391545480088581016173/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17689000000000000000000000000000000000000000
      center := (176890)
      previous := (88445)
      next := (88445)
      square := (1606106179183252604891762875797000000000000)
      linear := (-166479592294865441034342098027817100000000000)
      constant := (4432653962840069688369642149720542309595084197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree099.table
  base := (16758912541975876301916552197763720916981/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (2450)
      previous := (1225)
      next := (1225)
      square := (22245237938826213364151840385000000000000)
      linear := (-2308320389051387379109915593780500000000000)
      constant := (61524196911121473051819896974670344649864138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24720661623652209829/5000000000000000000)
  centralHi := (494413232473044196581/100000000000000000000)
  directionLo := (248464673298944090371/50000000000000000000)
  directionHi := (496929346597888180743/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree100.table
  base := (69215346527509704122106126982280164341731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-203474023531195090201853350537816381000000000000)
      constant := (5474110319876388654867866271402105863071946438739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree100.table
  base := (34607673235822847518441215616599134480407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (7350)
      previous := (3675)
      next := (3675)
      square := (66735713816478640092455521155000000000000)
      linear := (-6994874772104758807902795422551500000000000)
      constant := (188378469729114425593563225279290072768619829) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248464673298944090371/50000000000000000000)
  centralHi := (496929346597888180743/100000000000000000000)
  directionLo := (499432784842929308091/100000000000000000000)
  directionHi := (124858196210732327023/25000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree101.table
  base := (71426490662754205038396903687542263198793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-205507740385602996752152762461974071000000000000)
      constant := (5585840776540905835646043637158750077340537374617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree101.table
  base := (7142649061519313523597869784615264581301/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 147000000000000000000000000000000000000000
      center := (1470)
      previous := (735)
      next := (735)
      square := (13347142763295728018491104231000000000000)
      linear := (-1412957675411071095695168812752300000000000)
      constant := (38444656310641419428449669862446743893451247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499432784842929308091/100000000000000000000)
  centralHi := (124858196210732327023/25000000000000000000)
  directionLo := (62740467109768376649/12500000000000000000)
  directionHi := (501923736878147013193/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree102.table
  base := (73669082626664004193846231903745353476597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-207541457240010903302452174386131761000000000000)
      constant := (5698702665003103879700116485551063815475350444293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree102.table
  base := (73669082586175796184063702835786201072343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (4900)
      previous := (2450)
      next := (2450)
      square := (44490475877652426728303680770000000000000)
      linear := (-4756467988003968099365928469981000000000000)
      constant := (130738017469822157749586368031315523852544807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62740467109768376649/12500000000000000000)
  centralHi := (501923736878147013193/100000000000000000000)
  directionLo := (504402387690108970203/100000000000000000000)
  directionHi := (126100596922527242551/25000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree103.table
  base := (37971561204327054617669097806682084563921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-104787587047209404926375793155144725500000000000)
      constant := (2906347992620163498766119228264266270655995026849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree103.table
  base := (15188624474838052460888494193304787550699/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294000000000000000000000000000000000000000
      center := (2940)
      previous := (1470)
      next := (1470)
      square := (26694285526591456036982208462000000000000)
      linear := (-2881846234782619527848776538472600000000000)
      constant := (80011881473171277198027901121477603769952753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504402387690108970203/100000000000000000000)
  centralHi := (126100596922527242551/25000000000000000000)
  directionLo := (253434458871146126541/50000000000000000000)
  directionHi := (506868917742292253083/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree104.table
  base := (78248609999823032299186374175218282488163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-211608890948826716403050998234447141000000000000)
      constant := (5927820737233522720465098909629813544070906952147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree104.table
  base := (78248609970489928902970266836754870848223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-14549058383814290980389979974783000000000000)
      constant := (407982627974298181618598627060754966014688781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253434458871146126541/50000000000000000000)
  centralHi := (506868917742292253083/100000000000000000000)
  directionLo := (254661751564208336051/50000000000000000000)
  directionHi := (509323503128416672103/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree105.table
  base := (80585545392687796781305526831133940136751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4368100)
      previous := (2184050)
      next := (2184050)
      square := (39660989322688482692225164892130000000000000)
      linear := (-4360053220474175978639804288951119000000000000)
      constant := (123348508591156626884644663717930106639113420431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree105.table
  base := (16117109073544782967449835024367275600109/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (20)
      previous := (10)
      next := (10)
      square := (181593779092458884605321146000000000000)
      linear := (-19984878358796577308212350009800000000000)
      constant := (565964237052668408988032618913367275600109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254661751564208336051/50000000000000000000)
  centralHi := (509323503128416672103/100000000000000000000)
  directionLo := (127941578929789744281/25000000000000000000)
  directionHi := (4094130525753271817/800000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree106.table
  base := (16590785716192114274866211722039566220267/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4280738000000000000000000000000000000000000000
      center := (42807380)
      previous := (21403690)
      next := (21403690)
      square := (388677695362347130383806615942874000000000000)
      linear := (-43135264931528505900729964416552504200000000000)
      constant := (1232292907285264941794438928680303766511306658523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree106.table
  base := (16590785711943406800762940197832755817781/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 294000000000000000000000000000000000000000
      center := (2940)
      previous := (1470)
      next := (1470)
      square := (26694285526591456036982208462000000000000)
      linear := (-2965742560723335532536434907924600000000000)
      constant := (84812533228637586119149253677741015105213807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127941578929789744281/25000000000000000000)
  centralHi := (4094130525753271817/800000000000000000)
  directionLo := (514197523302593846663/100000000000000000000)
  directionHi := (64274690412824230833/12500000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree107.table
  base := (85353759559360395492975558510262375902331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-217710041512050436053949234006920211000000000000)
      constant := (6279983583601169491011946242699388753247696300139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree107.table
  base := (85353759541284371975943113081603872009819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-14968540013517871003828271822043000000000000)
      constant := (432219483701965949166497119013396769185443393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514197523302593846663/100000000000000000000)
  centralHi := (64274690412824230833/12500000000000000000)
  directionLo := (516617289718686417811/100000000000000000000)
  directionHi := (129154322429671604453/25000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree108.table
  base := (87785038323454486252099807561749437148013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-219743758366458342604248645931077901000000000000)
      constant := (6399634062481721272395760775105487999039055436797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree108.table
  base := (17557007661615005673208219258109467396301/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98000000000000000000000000000000000000000
      center := (980)
      previous := (490)
      next := (490)
      square := (8898095175530485345660736154000000000000)
      linear := (-1007224481561270956331624606964200000000000)
      constant := (29363611127293716930765353963628963902418749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516617289718686417811/100000000000000000000)
  centralHi := (129154322429671604453/25000000000000000000)
  directionLo := (259512887494070714179/50000000000000000000)
  directionHi := (519025774988141428359/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree109.table
  base := (90247764869524482138704819391808109369739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-221777475220866249154548057855235591000000000000)
      constant := (6520415973060021387410422113155944050243598893691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree109.table
  base := (90247764856440440340680411995623816135831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-15248194433320257686120466386883000000000000)
      constant := (448766715764971006244181888634623700971967157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259512887494070714179/50000000000000000000)
  centralHi := (519025774988141428359/100000000000000000000)
  directionLo := (260711567717947861253/50000000000000000000)
  directionHi := (521423135435895722507/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree110.table
  base := (23185484798613426928186731311907883988901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88445000000000000000000000000000000000000000
      center := (884450)
      previous := (442225)
      next := (442225)
      square := (8030530895916263024458814378985000000000000)
      linear := (-924839636674686593821683759418980500000000000)
      constant := (27447641798881814051904956320685869619759339578) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree110.table
  base := (92741939183323423230282802678268914420571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-15388021643221451027266563669303000000000000)
      constant := (457157130268212299868173852698735530419823937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260711567717947861253/50000000000000000000)
  centralHi := (521423135435895722507/100000000000000000000)
  directionLo := (523809523809523809523/100000000000000000000)
  directionHi := (130952380952380952381/25000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree111.table
  base := (47633780647816079198465512401912803317943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-112922454464841031127573440851775485500000000000)
      constant := (3382687044642133869480196093933616862924822340967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree111.table
  base := (2381689032154116786507558480919445891551/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49000000000000000000000000000000000000000
      center := (490)
      previous := (245)
      next := (245)
      square := (4449047587765242672830368077000000000000)
      linear := (-517594961770754812280422031724100000000000)
      constant := (15520847013958447230466598335627311394743996) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523809523809523809523/100000000000000000000)
  centralHi := (130952380952380952381/25000000000000000000)
  directionLo := (263092544696405131663/50000000000000000000)
  directionHi := (526185089392810263327/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree112.table
  base := (1222807889635955283015069865233048726139/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43681000000000000000000000000000000000000000
      center := (436810)
      previous := (218405)
      next := (218405)
      square := (3966098932268848269222516489213000000000000)
      linear := (-465058419967530548582543456383078900000000000)
      constant := (14060306724326437339209445198375967211251821272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree112.table
  base := (19564926232564794976011907615245879404597/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6000000000000000000000000000000000000000
      center := (60)
      previous := (30)
      next := (30)
      square := (544781337277376653815963438000000000000)
      linear := (-63949698216423827385954115241400000000000)
      constant := (1935394107005223455059201210842537638213791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263092544696405131663/50000000000000000000)
  centralHi := (526185089392810263327/100000000000000000000)
  directionLo := (26427498905736396089/5000000000000000000)
  directionHi := (528549978114727921781/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree113.table
  base := (20082629763672439124339343119310878223357/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4280738000000000000000000000000000000000000000
      center := (42807380)
      previous := (21403690)
      next := (21403690)
      square := (388677695362347130383806615942874000000000000)
      linear := (-45982468527699575071149141110373270200000000000)
      constant := (1402971586446510797365227429190068819712048398733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree113.table
  base := (100413148811513836976551328646924531718323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-15807503272925031050704855516563000000000000)
      constant := (482795567660528526607281441090736906162593481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26427498905736396089/5000000000000000000)
  centralHi := (528549978114727921781/100000000000000000000)
  directionLo := (530904332654047006193/100000000000000000000)
  directionHi := (265452166327023503097/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree114.table
  base := (51516557118283703463271351288056216531051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29645000000000000000000000000000000000000000
      center := (296450)
      previous := (148225)
      next := (148225)
      square := (2691673790597971817062372686585000000000000)
      linear := (-321254930045575875216128971573440500000000000)
      constant := (9890993076480344900935669205296814807812601379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree114.table
  base := (20606622846148709014844798055461327926971/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98000000000000000000000000000000000000000
      center := (980)
      previous := (490)
      next := (490)
      square := (8898095175530485345660736154000000000000)
      linear := (-1063155365521748292790063519932200000000000)
      constant := (32766496316752041500268199095536405068421579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530904332654047006193/100000000000000000000)
  centralHi := (265452166327023503097/50000000000000000000)
  directionLo := (26662414626989367983/5000000000000000000)
  directionHi := (533248292539787359661/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree115.table
  base := (52842263712112147579093462701419406080387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-116989888173656844228172264700090865500000000000)
      constant := (3634433750938002956983074666328486297772871842803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree115.table
  base := (105684527419272049092068475644103968796571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-16087157692727417732997050081403000000000000)
      constant := (500277187488353599817820602726828283413095937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26662414626989367983/5000000000000000000)
  centralHi := (533248292539787359661/100000000000000000000)
  directionLo := (535581994247713929477/100000000000000000000)
  directionHi := (267790997123856964739/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree116.table
  base := (108367388380279024118882797272450419707231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-236013493201721595006643941324339421000000000000)
      constant := (7397569434201889074969190980996664378378346308239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree116.table
  base := (54183694188034131868217056367354916584429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (7350)
      previous := (3675)
      next := (3675)
      square := (66735713816478640092455521155000000000000)
      linear := (-8113492451314305537071573681911500000000000)
      constant := (254567397935797944505253820593115172737911063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535581994247713929477/100000000000000000000)
  centralHi := (267790997123856964739/50000000000000000000)
  directionLo := (134476392823266082781/25000000000000000000)
  directionHi := (4303244570344514649/800000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree117.table
  base := (11108169710385765589452858018937686218253/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2140369000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (194338847681173565191903307971437000000000000)
      linear := (-23804721005612950155694335324849711100000000000)
      constant := (752740279819458795186541008839153463213275955357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree117.table
  base := (11108169710027762672045227076762588690113/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49000000000000000000000000000000000000000
      center := (490)
      previous := (245)
      next := (245)
      square := (4449047587765242672830368077000000000000)
      linear := (-545560403750993480509641488208100000000000)
      constant := (17269008996696062314197147102879066845815537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134476392823266082781/25000000000000000000)
  centralHi := (4303244570344514649/800000000000000000)
  directionLo := (67527394289960846487/12500000000000000000)
  directionHi := (540219154319686771897/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree118.table
  base := (113827453594237482161524518501822638862601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1943388476811735651919033079714370000000000000)
      linear := (-240080926910537408107242765172654801000000000000)
      constant := (7658367593852555682162931769436905472719706439769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree118.table
  base := (113827453591193929098306630436919604683789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-16506639322430997756435341928663000000000000)
      constant := (527083609576107728349005919489281181888516983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67527394289960846487/12500000000000000000)
  centralHi := (540219154319686771897/100000000000000000000)
  directionLo := (542522871185756728377/100000000000000000000)
  directionHi := (271261435592878364189/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree119.table
  base := (7287791115676429490604806253656965165293/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (2184050)
      previous := (1092025)
      next := (1092025)
      square := (19830494661344241346112582446065000000000000)
      linear := (-2470557589438217496505532419355229500000000000)
      constant := (79494528787495075465139556924992467163081308264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree119.table
  base := (116604657848235588461675833327294482817323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (300)
      previous := (150)
      next := (150)
      square := (2723906686386883269079817190000000000000)
      linear := (-339723806782289614236355902267000000000000)
      constant := (10942343161167101493178753483834883448451969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542522871185756728377/100000000000000000000)
  centralHi := (271261435592878364189/50000000000000000000)
  directionLo := (136204211761557878733/25000000000000000000)
  directionHi := (544816847046231514933/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree120.table
  base := (59706654936562462742624563496063716669961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-122074180309676610603920794510485090500000000000)
      constant := (3961845740079713333424971193893967311185167755609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree120.table
  base := (59706654935462833049221580289840380726023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (2450)
      previous := (1225)
      next := (1225)
      square := (22245237938826213364151840385000000000000)
      linear := (-2797715623705564073121256082250500000000000)
      constant := (90890647644008748980915376511662178655575127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136204211761557878733/25000000000000000000)
  centralHi := (544816847046231514933/100000000000000000000)
  directionLo := (5471012044321932057/1000000000000000000)
  directionHi := (547101204432193205701/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree121.table
  base := (15281676207593042247061325505097758008861/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88445000000000000000000000000000000000000000
      center := (884450)
      previous := (442225)
      next := (442225)
      square := (8030530895916263024458814378985000000000000)
      linear := (-1017281311875045982471657028698875500000000000)
      constant := (33297729631431524114552909367862937465674968916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree121.table
  base := (122253409658875039079974106759904251685139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-16926120952134577779873633775923000000000000)
      constant := (554590822476644089437696662276648924997715433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5471012044321932057/1000000000000000000)
  centralHi := (547101204432193205701/100000000000000000000)
  directionLo := (5493760633272222389/1000000000000000000)
  directionHi := (549376063327222238901/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree122.table
  base := (31281239303339241386788150664575480104031/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-124107897164084517154220206434642780500000000000)
      constant := (4096770546557415057454517950742152935049569454878) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree122.table
  base := (125124957211768230842401046672784875572779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-17065948162035771121019731058343000000000000)
      constant := (563915624734916384767483589424245376709198513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5493760633272222389/1000000000000000000)
  centralHi := (549376063327222238901/100000000000000000000)
  directionLo := (551641541240936401763/100000000000000000000)
  directionHi := (137910385310234100441/25000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree123.table
  base := (16003494066337708964752826337524539195391/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-125124755591288470429369912396721625500000000000)
      constant := (4165081523542035787993381142883084120732399357116) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree123.table
  base := (128027952529351481872984874396391726864853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (4900)
      previous := (2450)
      next := (2450)
      square := (44490475877652426728303680770000000000000)
      linear := (-5735258457312321487388609446921000000000000)
      constant := (191106097546277359075493463980746194616377797) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551641541240936401763/100000000000000000000)
  centralHi := (137910385310234100441/25000000000000000000)
  directionLo := (138474438319955683019/25000000000000000000)
  directionHi := (553897753279822732077/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree124.table
  base := (26192479122514018799530304764001473692577/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4280738000000000000000000000000000000000000000
      center := (42807380)
      previous := (21403690)
      next := (21403690)
      square := (388677695362347130383806615942874000000000000)
      linear := (-50456645607396969481807847343520188200000000000)
      constant := (1693583286542741449267504558369498857045907340913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree124.table
  base := (65481197805711353945938748109853268196039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (7350)
      previous := (3675)
      next := (3675)
      square := (66735713816478640092455521155000000000000)
      linear := (-8672801290919078901655962811591500000000000)
      constant := (291399413094180730212774700027554430424817733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138474438319955683019/25000000000000000000)
  centralHi := (553897753279822732077/100000000000000000000)
  directionLo := (69518101526935393233/12500000000000000000)
  directionHi := (111228962443096629173/20000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree125.table
  base := (66964143229399014611521387987845629242351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-127158472445696376979669324320879315500000000000)
      constant := (4303400625001692835300768811332720349115821567519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree125.table
  base := (133928286457823048360199457021626291439157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-17485429791739351144458022905603000000000000)
      constant := (592357225383481181865475333860054064841556079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69518101526935393233/12500000000000000000)
  centralHi := (111228962443096629173/20000000000000000000)
  directionLo := (111676565710081656061/20000000000000000000)
  directionHi := (279191414275204140153/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree126.table
  base := (136925625069258182934557142786743991587929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4368100)
      previous := (2184050)
      next := (2184050)
      square := (39660989322688482692225164892130000000000000)
      linear := (-5231646158077564500196695113590129000000000000)
      constant := (178506479570466007993133127166774133296552326649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree126.table
  base := (68462812534214877436024954252034641946267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (50)
      previous := (25)
      next := (25)
      square := (453984447731147211513302865000000000000)
      linear := (-59949853747076681923823538054500000000000)
      constant := (2047596905524398631056431185909034641946267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111676565710081656061/20000000000000000000)
  centralHi := (279191414275204140153/50000000000000000000)
  directionLo := (5606119105813880991/1000000000000000000)
  directionHi := (560611910581388099101/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree127.table
  base := (34988602860963517040950538666000034037429/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-129192189300104283529968736245037005500000000000)
      constant := (4443982589780923445903714197812438679705315742602) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree127.table
  base := (139954411443150208370326057395496604302537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-17765084211541737826750217470443000000000000)
      constant := (611707620710423892419501593835799000832472939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5606119105813880991/1000000000000000000)
  centralHi := (560611910581388099101/100000000000000000000)
  directionLo := (562832164460662218559/100000000000000000000)
  directionHi := (1758850513939569433/312500000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree128.table
  base := (1787683069781435909102630452970281205687/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2140369000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (194338847681173565191903307971437000000000000)
      linear := (-26041809545461647361023688441423170100000000000)
      constant := (903024429183027160683286356537131211311480628024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree128.table
  base := (143014645581916887318283340633644727337711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (14700)
      previous := (7350)
      next := (7350)
      square := (133471427632957280184911042310000000000000)
      linear := (-17904911421442931167896314752863000000000000)
      constant := (621499616842223340866306358625529774918643517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell114.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562832164460662218559/100000000000000000000)
  centralHi := (1758850513939569433/312500000000000000)
  directionLo := (113008738850981530647/20000000000000000000)
  directionHi := (141260923563726913309/25000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 1531
  qDenominator := 2926
  table := BinomialMassData.Q1531_2926.Degree129.table
  base := (73053163742595571273593449052412382911043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (971694238405867825959516539857185000000000000)
      linear := (-131225906154512190080268148169194695500000000000)
      constant := (4586827417879001343379399754750642234098926194867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1531_2926.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 11
  qDenominator := 21
  table := BinomialMassData.Q11_21.Degree129.table
  base := (73053163742341568466732366066035335867127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (2450)
      previous := (1225)
      next := (1225)
      square := (22245237938826213364151840385000000000000)
      linear := (-3007456438557354084840402005880500000000000)
      constant := (105228246436594114102997313365290231457489223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11_21.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell114.Kernel129
