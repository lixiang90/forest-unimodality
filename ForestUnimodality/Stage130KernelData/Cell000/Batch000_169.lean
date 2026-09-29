import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell000.Parameters
import ForestUnimodality.BinomialMassData.Q1_4.Batch000_049
import ForestUnimodality.BinomialMassData.Q1_4.Batch050_099
import ForestUnimodality.BinomialMassData.Q1_4.Batch100_149
import ForestUnimodality.BinomialMassData.Q1_4.Batch150_199
import ForestUnimodality.BinomialMassData.Q9_35.Batch000_049
import ForestUnimodality.BinomialMassData.Q9_35.Batch050_099
import ForestUnimodality.BinomialMassData.Q9_35.Batch100_149
import ForestUnimodality.BinomialMassData.Q9_35.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree000.table
  base := (484995848530642047590433207/100000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (803350737397137137918434760000000000000)
      constant := (193998339412256819036173282800000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree000.table
  base := (484995848530642047590433207/100000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (494)
      previous := (171)
      next := (0)
      square := (5488711190527294572771843600000000000000)
      linear := (7029318952224949956786304150000000000000)
      constant := (1697485469857247166566516224500000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree001.table
  base := (19256286820376833027820067109089081632653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (489710097938434590902900840000000000000)
      constant := (153888661958597717756457869922712653061224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree001.table
  base := (38231592911341263460525351973606734693877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (29445872379676389235525492090000000000000)
      constant := (9356627978344220128537321710815649999999865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (1102657790843584099/4000000000000000000)
  directionHi := (6891611192772400619/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree002.table
  base := (1530946412915688219137431491412993877551/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (176069458479732043887366920000000000000)
      constant := (122230857984285840235543068893039510204080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree002.table
  base := (30178505802315895022063838155493020408163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (9686512093778128773546855130000000000000)
      constant := (7378590330057846423084512952163789999999935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1102657790843584099/4000000000000000000)
  centralHi := (6891611192772400619/25000000000000000000)
  directionLo := (7796968012336761079/20000000000000000000)
  directionHi := (9746210015420951349/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree003.table
  base := (24346276815966684290246246373645943469387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-137571180978970503128167000000000000000)
      constant := (97135439930209924672938635084583773877548) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree003.table
  base := (2382626925072062746407121843952258671137/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-10072848192120131688431781830000000000000)
      constant := (5822342046701078414608234898041033744285650) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7796968012336761079/20000000000000000000)
  centralHi := (9746210015420951349/25000000000000000000)
  directionLo := (4774648292756860073/10000000000000000000)
  directionHi := (47746482927568600731/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree004.table
  base := (1208295241580973191124533359323308205389/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-451211820437673050143700920000000000000)
      constant := (77154826002702552188082768076691725144896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree004.table
  base := (9392249473278934530785635194607760515879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-29832208478018392150410418790000000000000)
      constant := (4592238972324506130489313051509802652780710) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4774648292756860073/10000000000000000000)
  centralHi := (47746482927568600731/100000000000000000000)
  directionLo := (55132889542179204951/100000000000000000000)
  directionHi := (6891611192772400619/12500000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree005.table
  base := (15300404159995416342677901700334660838341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-764852459896375597159234840000000000000)
      constant := (61177555216543689407737106851338643353364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree005.table
  base := (3689006486710122092508886345916009089193/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-49591568763916652612389055750000000000000)
      constant := (3615474715896282366818277500447688907409140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55132889542179204951/100000000000000000000)
  centralHi := (6891611192772400619/12500000000000000000)
  directionLo := (15410111101537495139/25000000000000000000)
  directionHi := (61640444406149980557/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree006.table
  base := (6025160410061730511727670486475597977683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-1078493099355078144174768760000000000000)
      constant := (48407640051962299848513614391804783821464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree006.table
  base := (11528912105733231752172208571655510351137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-69350929049814913074367692710000000000000)
      constant := (2840124431686769982458628706307600036028565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15410111101537495139/25000000000000000000)
  centralHi := (61640444406149980557/100000000000000000000)
  directionLo := (4220232731986434701/6250000000000000000)
  directionHi := (67523723711782955217/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree007.table
  base := (4710194377769394428717191893943264531399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-1392133738813780691190302680000000000000)
      constant := (38196740148394718538850419581546116251192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree007.table
  base := (4466256322417375715022141408885734791929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (494)
      previous := (171)
      next := (0)
      square := (5488711190527294572771843600000000000000)
      linear := (-12730041333673310505192332810000000000000)
      constant := (317768592712519824545115324416001435435030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4220232731986434701/6250000000000000000)
  centralHi := (67523723711782955217/100000000000000000000)
  directionLo := (72933957394499943593/100000000000000000000)
  directionHi := (36466978697249971797/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree008.table
  base := (3634679303350860370330124836530452891953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-1705774378272483238205836600000000000000)
      constant := (29979858067682229062928400532243623135624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree008.table
  base := (1705003865158202627386268509347991362623/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-108869649621611433998324966630000000000000)
      constant := (1732272902438390695833673143529031535370540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72933957394499943593/100000000000000000000)
  centralHi := (36466978697249971797/50000000000000000000)
  directionLo := (7796968012336761079/10000000000000000000)
  directionHi := (77969680123367610791/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree009.table
  base := (5498319930749431392268598254327224675073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-2019415017731185785221370520000000000000)
      constant := (23361352038373530297290195747308898700292) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree009.table
  base := (5088980696208870691344843141768124583091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-128629009907509694460303603590000000000000)
      constant := (1338704927093983871176440247415190522857295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7796968012336761079/10000000000000000000)
  centralHi := (77969680123367610791/100000000000000000000)
  directionLo := (41349667156634403713/50000000000000000000)
  directionHi := (82699334313268807427/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree010.table
  base := (2015077598229464291009195949576662902323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-2333055657189888332236904440000000000000)
      constant := (18032751935576653320971654696613303218584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree010.table
  base := (732025494503053735763474176694825888841/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-148388370193407954922282240550000000000000)
      constant := (1024252407587740790170684866951161713830225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41349667156634403713/50000000000000000000)
  centralHi := (82699334313268807427/100000000000000000000)
  directionLo := (43586376234941041661/50000000000000000000)
  directionHi := (87172752469882083323/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree011.table
  base := (701135553963041069170787141132521516521/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-2646696296648590879252438360000000000000)
      constant := (13752769007379406001066849208120344264336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree011.table
  base := (77246153572719765063038038596441154263/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-168147730479306215384260877510000000000000)
      constant := (773828519489543315279774195418098649421920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43586376234941041661/50000000000000000000)
  centralHi := (87172752469882083323/100000000000000000000)
  directionLo := (91427554109758761193/100000000000000000000)
  directionHi := (45713777054879380597/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree012.table
  base := (1774123198703086509675061946098203394007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-2960336936107293426267972280000000000000)
      constant := (10331972092877580471224554064392813576028) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree012.table
  base := (1476207011794772580320437567469012962023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-187907090765204475846239514470000000000000)
      constant := (575667870386291013950841798677908175695635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91427554109758761193/100000000000000000000)
  centralHi := (45713777054879380597/50000000000000000000)
  directionLo := (95492965855137201461/100000000000000000000)
  directionHi := (47746482927568600731/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree013.table
  base := (28174099641621045180499366450036118797/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-3273977575565995973283506200000000000000)
      constant := (7621053366151889390572159995604623206016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree013.table
  base := (7943823245942239018970973597484657561/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-207666451051102736308218151430000000000000)
      constant := (420555543493421972392595948488699288195600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95492965855137201461/100000000000000000000)
  centralHi := (47746482927568600731/50000000000000000000)
  directionLo := (99392230104409734567/100000000000000000000)
  directionHi := (12424028763051216821/12500000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree014.table
  base := (39335551995685443530755370309779345263/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-3587618215024698520299040120000000000000)
      constant := (5501836917779199515658145304956469524208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree014.table
  base := (-39909752502273832370265135168340361807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (494)
      previous := (171)
      next := (0)
      square := (5488711190527294572771843600000000000000)
      linear := (-32489401619571570967170969770000000000000)
      constant := (43034466126064749552773838654216174673510) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99392230104409734567/100000000000000000000)
  centralHi := (12424028763051216821/12500000000000000000)
  directionLo := (6446511981552706427/6250000000000000000)
  directionHi := (103144191704843302833/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree015.table
  base := (-241024846659028755986463732145582536649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-3901258854483401067314574040000000000000)
      constant := (3880378946264514819726051292835339706808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree015.table
  base := (-693163278904713704743895628468441027391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-247185171622899257232175425350000000000000)
      constant := (211993450371756885440325928175231948289205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6446511981552706427/6250000000000000000)
  centralHi := (103144191704843302833/100000000000000000000)
  directionLo := (106764381512576558771/100000000000000000000)
  directionHi := (26691095378144139693/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree016.table
  base := (-1035358720922660490809356560595073446463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-4214899493942103614330107960000000000000)
      constant := (2681662629399290989585920157619706214148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree016.table
  base := (-1223109537324193506374211352883253253963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-266944531908797517694154062310000000000000)
      constant := (148259007513059633674283795535602952779065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106764381512576558771/100000000000000000000)
  centralHi := (26691095378144139693/25000000000000000000)
  directionLo := (55132889542179204951/50000000000000000000)
  directionHi := (110265779084358409903/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree017.table
  base := (-758814729439160885082406162276261551507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-4528540133400806161345641880000000000000)
      constant := (1845509630994509594123565831789907587944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree017.table
  base := (-421123609627297766996979990918352689611/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-286703892194695778156132699270000000000000)
      constant := (106403075536041511973962055238014364181220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55132889542179204951/50000000000000000000)
  centralHi := (110265779084358409903/100000000000000000000)
  directionLo := (113659363513958082779/100000000000000000000)
  directionHi := (5682968175697904139/5000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree018.table
  base := (-970493331842988538196242621293525746747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-4842180772859508708361175800000000000000)
      constant := (1323420925046427727926226369651794026024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree018.table
  base := (-417844226193173496411192744037130216593/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-306463252480594038618111336230000000000000)
      constant := (83509383056693052683979853742515484673575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113659363513958082779/100000000000000000000)
  centralHi := (5682968175697904139/5000000000000000000)
  directionLo := (23390904037010283237/20000000000000000000)
  directionHi := (58477260092525708093/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree019.table
  base := (-1157623659987777873639051717915685915267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-5155821412318211255376709720000000000000)
      constant := (1076128573035328039850989286674512677864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree019.table
  base := (-2446886981822983288719102486315516594751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-326222612766492299080089973190000000000000)
      constant := (77226575128467923469851024394698434286005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23390904037010283237/20000000000000000000)
  centralHi := (58477260092525708093/50000000000000000000)
  directionLo := (24031869397974958561/20000000000000000000)
  directionHi := (60079673494937396403/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree020.table
  base := (-264839647038928632100717005196160376719/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-5469462051776913802392243640000000000000)
      constant := (1071692404392296377155841992153584931240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree020.table
  base := (-691317017542589027937833185000465789231/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-345981973052390559542068610150000000000000)
      constant := (85649512374360806506946430099543526553620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24031869397974958561/20000000000000000000)
  centralHi := (60079673494937396403/50000000000000000000)
  directionLo := (15410111101537495139/12500000000000000000)
  directionHi := (123280888812299961113/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree021.table
  base := (-1473479207800529660611895008516069918921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-5783102691235616349407777560000000000000)
      constant := (1284015216421770645264364781871440648632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree021.table
  base := (-122027794596454880548269844246342293831/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (494)
      previous := (171)
      next := (0)
      square := (5488711190527294572771843600000000000000)
      linear := (-52248761905469831429149606730000000000000)
      constant := (15318175701863159495644803250450492897875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15410111101537495139/12500000000000000000)
  centralHi := (123280888812299961113/100000000000000000000)
  directionLo := (126325319804337716951/100000000000000000000)
  directionHi := (15790664975542214619/12500000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree022.table
  base := (-80407184031488281586254293008466512419/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-6096743330694318896423311480000000000000)
      constant := (1691680186529124782087724098645358012960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree022.table
  base := (-3308344722422731929154773463246132617963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-385500693624187080466025884070000000000000)
      constant := (140691275432220124388042037132697508599065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126325319804337716951/100000000000000000000)
  centralHi := (15790664975542214619/12500000000000000000)
  directionLo := (12929808699662084439/10000000000000000000)
  directionHi := (129298086996620844391/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree023.table
  base := (-3460795885060075984121261586417103679457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-6410383970153021443438845400000000000000)
      constant := (2277037003932863441886134244331585282172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree023.table
  base := (-3542470610540326779868253952741623370391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-405260053910085340928004521030000000000000)
      constant := (184999671812101554428186083576302274254205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12929808699662084439/10000000000000000000)
  centralHi := (129298086996620844391/100000000000000000000)
  directionLo := (132204024818850600581/100000000000000000000)
  directionHi := (66102012409425300291/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree024.table
  base := (-3684135267860905151905532614582683174473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-6724024609611723990454379320000000000000)
      constant := (3025480545200139949985703221669267302108) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree024.table
  base := (-939145194533639662633849208319270532979/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-425019414195983601389983157990000000000000)
      constant := (239292898079437895841334493719114877680580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132204024818850600581/100000000000000000000)
  centralHi := (66102012409425300291/50000000000000000000)
  directionLo := (4220232731986434701/3125000000000000000)
  directionHi := (135047447423565910433/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree025.table
  base := (-388933844372301415140957904201451094827/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-7037665249070426537469913240000000000000)
      constant := (3924879074086972767960054081941956206920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree025.table
  base := (-1976790279267135785435214482827454780541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-444778774481881861851961794950000000000000)
      constant := (302859147568662361347501686664547157534910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4220232731986434701/3125000000000000000)
  centralHi := (135047447423565910433/100000000000000000000)
  directionLo := (137832223855448012377/100000000000000000000)
  directionHi := (68916111927724006189/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree026.table
  base := (-4078933822331319936533123031353767943849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-7351305888529129084485447160000000000000)
      constant := (4965118951853694080210298174584928224604) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree026.table
  base := (-2067942415843509333359065102763159804343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-464538134767780122313940431910000000000000)
      constant := (375106774692624435114716597778051695871930) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137832223855448012377/100000000000000000000)
  centralHi := (68916111927724006189/50000000000000000000)
  directionLo := (35140459952040917893/25000000000000000000)
  directionHi := (140561839808163671573/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree027.table
  base := (-4255036332441415301545062890116128977069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-7664946527987831631500981080000000000000)
      constant := (6137740463477932709660842269535484091724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree027.table
  base := (-2152753829016292318647247095875543835981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-484297495053678382775919068870000000000000)
      constant := (455542334643576865835060785538983520369310) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35140459952040917893/25000000000000000000)
  centralHi := (140561839808163671573/100000000000000000000)
  directionLo := (143239448782705802191/100000000000000000000)
  directionHi := (8952465548919112637/6250000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree028.table
  base := (-4419420582397584437489061543073004762823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-7978587167446534178516515000000000000000)
      constant := (7435645175582551892137034667707980948708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree028.table
  base := (-1116033518673257513356767133735123082899/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (494)
      previous := (171)
      next := (0)
      square := (5488711190527294572771843600000000000000)
      linear := (-72008122191368091891128243690000000000000)
      constant := (77678999046659259093683583621082768394140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143239448782705802191/100000000000000000000)
  centralHi := (8952465548919112637/6250000000000000000)
  directionLo := (145867914788999887187/100000000000000000000)
  directionHi := (36466978697249971797/25000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree029.table
  base := (-4573579924206871558514391128071016038359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-8292227806905236725532048920000000000000)
      constant := (8852859680139374771041786817715935846564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree029.table
  base := (-461317789042329726971448550247679337559/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-523816215625474903699876342790000000000000)
      constant := (639392367596777401700224591695185622980450) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145867914788999887187/100000000000000000000)
  centralHi := (36466978697249971797/25000000000000000000)
  directionLo := (148449848239088696243/100000000000000000000)
  directionHi := (37112462059772174061/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree030.table
  base := (-4718774358557800982718183322058139029093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-8605868446363939272547582840000000000000)
      constant := (10384343974394304073986572011767443883628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree030.table
  base := (-4753828438879340319446746846939824722651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-543575575911373164161854979750000000000000)
      constant := (742169070708355891812328875199742942950505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148449848239088696243/100000000000000000000)
  centralHi := (37112462059772174061/25000000000000000000)
  directionLo := (37746909078365276277/25000000000000000000)
  directionHi := (150987636313461105109/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree031.table
  base := (-1214017391765044100463262991405445466517/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-8919509085822641819563116760000000000000)
      constant := (12025835331908125033960934887512872535728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree031.table
  base := (-4887088581936862068957755140168068475897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-563334936197271424623833616710000000000000)
      constant := (851837401501803081740291805760823223405235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37746909078365276277/25000000000000000000)
  centralHi := (150987636313461105109/100000000000000000000)
  directionLo := (76741734403197345023/50000000000000000000)
  directionHi := (153483468806394690047/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree032.table
  base := (-4986368857550085023380924692200645821103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-9233149725281344366578650680000000000000)
      constant := (13773720521336488821117164911197416715588) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree032.table
  base := (-1253451436209547332716533583364703824357/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-583094296483169685085812253670000000000000)
      constant := (968189740792748902392550515310590252130140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76741734403197345023/50000000000000000000)
  centralHi := (153483468806394690047/100000000000000000000)
  directionLo := (7796968012336761079/5000000000000000000)
  directionHi := (155939360246735221581/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree033.table
  base := (-1277609855678265861059468899579176412193/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-9546790364740046913594184600000000000000)
      constant := (15624930771937249047710965696733177404912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree033.table
  base := (-2567348687200128235415337566579130103299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-602853656769067945547790890630000000000000)
      constant := (1091050314111044434182701280794226249383490) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7796968012336761079/5000000000000000000)
  centralHi := (155939360246735221581/100000000000000000000)
  directionLo := (39589292232463722109/25000000000000000000)
  directionHi := (158357168929854888437/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree034.table
  base := (-2614467007177023589516246884194996370013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-9860431004198749460609718520000000000000)
      constant := (17576855076490663655307980906440029039896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree034.table
  base := (-5250371911465631810798896134293164638797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-622613017054966206009769527590000000000000)
      constant := (1220270053450260438233602046430174663494735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39589292232463722109/25000000000000000000)
  centralHi := (158357168929854888437/100000000000000000000)
  directionLo := (160738613372133242743/100000000000000000000)
  directionHi := (20092326671516655343/12500000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree035.table
  base := (-5342408904761279938806238581477541152511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-10174071643657452007625252440000000000000)
      constant := (19627268345843757799742373024089835389956) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree035.table
  base := (-5361346137452198393352070357173991193053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (494)
      previous := (171)
      next := (0)
      square := (5488711190527294572771843600000000000000)
      linear := (-91767482477266352353106880650000000000000)
      constant := (193674621051859367016120131748910308243145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160738613372133242743/100000000000000000000)
  centralHi := (20092326671516655343/12500000000000000000)
  directionLo := (81542643301087660111/50000000000000000000)
  directionHi := (163085286602175320223/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree036.table
  base := (-5451338827103410812625548179629460272623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-10487712283116154554640786360000000000000)
      constant := (21774271647321935124748389481482158909508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree036.table
  base := (-218722383033873911925504731559974161153/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-662131737626762726933726801510000000000000)
      constant := (1497299512595021389806799888867158262937875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81542643301087660111/50000000000000000000)
  centralHi := (163085286602175320223/100000000000000000000)
  directionLo := (165398668626537614853/100000000000000000000)
  directionHi := (82699334313268807427/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree037.table
  base := (-555612944674490620999709713253611840233/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-10801352922574857101656320280000000000000)
      constant := (24016242319467329992299331999855526390680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree037.table
  base := (-17409020282524402644731861904363685327/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-681891097912660987395705438470000000000000)
      constant := (1644909854525511839131608255795887070363200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165398668626537614853/100000000000000000000)
  centralHi := (82699334313268807427/50000000000000000000)
  directionLo := (167680137347119117797/100000000000000000000)
  directionHi := (83840068673559558899/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree038.table
  base := (-5657127805684867653994618066113264431253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-11114993562033559648671854200000000000000)
      constant := (26351792194283536310100270075546942274988) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree038.table
  base := (-2835072956661540673082974843123249687267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-701650458198559247857684075430000000000000)
      constant := (1798475210268426964057650064897607653239170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167680137347119117797/100000000000000000000)
  centralHi := (83840068673559558899/50000000000000000000)
  directionLo := (10620686134935979131/6250000000000000000)
  directionHi := (169930978158975666097/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree039.table
  base := (-2877315548045548277366448631000735838083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-11428634201492262195687388120000000000000)
      constant := (28779732503099348437692058581994113295336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree039.table
  base := (-5766110051523694676728181177335743810963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-721409818484457508319662712390000000000000)
      constant := (1957928889125664566721276508014742766314065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10620686134935979131/6250000000000000000)
  centralHi := (169930978158975666097/100000000000000000000)
  directionLo := (43038098104603639469/25000000000000000000)
  directionHi := (172152392418414557877/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree040.table
  base := (-5848894050820506363136967745576316634437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-11742274840950964742702922040000000000000)
      constant := (31299044314487112571374565417694733462252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree040.table
  base := (-58590113523839303677977126494378954787/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-741169178770355768781641349350000000000000)
      constant := (2123213941490525672322266105287715607718500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43038098104603639469/25000000000000000000)
  centralHi := (172152392418414557877/100000000000000000000)
  directionLo := (34869100987952833329/20000000000000000000)
  directionHi := (87172752469882083323/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree041.table
  base := (-1188027036966930964379507662822842881749/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-12055915480409667289718455960000000000000)
      constant := (33908853568600597740384955393543142365020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree041.table
  base := (-594904845705780270394408926678039454991/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-760928539056254029243619986310000000000000)
      constant := (2294281700280276781141080291480803335272050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34869100987952833329/20000000000000000000)
  centralHi := (87172752469882083323/50000000000000000000)
  directionLo := (176511370653617849919/100000000000000000000)
  directionHi := (551598033292555781/312500000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree042.table
  base := (-3014271039212064088849983885524241510087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-12369556119868369836733989880000000000000)
      constant := (36608409944277458957981793295806067919304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree042.table
  base := (-6036391227575389422062462623836858869287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (494)
      previous := (171)
      next := (0)
      square := (5488711190527294572771843600000000000000)
      linear := (-111526842763164612815085517610000000000000)
      constant := (353012935613935549662629560849709939574955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176511370653617849919/100000000000000000000)
  centralHi := (551598033292555781/312500000000000000)
  directionLo := (89325490269206468549/50000000000000000000)
  directionHi := (178650980538412937099/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree043.table
  base := (-305713792937728815331046530950668637279/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-12683196759327072383749523800000000000000)
      constant := (39397068932855096719858381113946509017680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree043.table
  base := (-3060592500081030165220630184982933976047/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-800447259628050550167577260230000000000000)
      constant := (2653604881167126268783581234596362351736970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89325490269206468549/50000000000000000000)
  centralHi := (178650980538412937099/100000000000000000000)
  directionLo := (22595658364998300629/12500000000000000000)
  directionHi := (180765266919986405033/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree044.table
  base := (-1239495001718928037375113020343477955029/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-12996837398785774930765057720000000000000)
      constant := (42274276603258947113154165873130440899420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree044.table
  base := (-3101777095106292760063190599351285980871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-820206619913948810629555897190000000000000)
      constant := (2841794214117290372270358037509869869373210) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22595658364998300629/12500000000000000000)
  centralHi := (180765266919986405033/100000000000000000000)
  directionLo := (182855108219517522387/100000000000000000000)
  directionHi := (45713777054879380597/25000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree045.table
  base := (-39239116304714000999505704083294539591/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-13310478038244477477780591640000000000000)
      constant := (45239556632249328772040981836691494661760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree045.table
  base := (-6283605352536986727824129127443086284793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-839965980199847071091534534150000000000000)
      constant := (3035632442219585832605692850426443860225715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (182855108219517522387/100000000000000000000)
  centralHi := (45713777054879380597/25000000000000000000)
  directionLo := (184921333218449941669/100000000000000000000)
  directionHi := (18492133321844994167/10000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree046.table
  base := (-3178364551321547121308302785270408745881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-13624118677703180024796125560000000000000)
      constant := (48292499246187369629080299817836730032952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree046.table
  base := (-6361429782803376533362887397084835440779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-859725340485745331553513171110000000000000)
      constant := (3235097198035325067731631779326215317009145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (184921333218449941669/100000000000000000000)
  centralHi := (18492133321844994167/10000000000000000000)
  directionLo := (93482362449563889843/50000000000000000000)
  directionHi := (186964724899127779687/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree047.table
  base := (-804121832073959385262259961916944743961/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-13937759317161882571811659480000000000000)
      constant := (51432751779751179095730376448657768193248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree047.table
  base := (-643710573168729292427366453779162859691/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-879484700771643592015491808070000000000000)
      constant := (3440169310149001270703077734319050993757050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93482362449563889843/50000000000000000000)
  centralHi := (186964724899127779687/100000000000000000000)
  directionLo := (11811626494476358809/6250000000000000000)
  directionHi := (37797204782324348189/20000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree048.table
  base := (-6507071177486457451937683649928489422497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-14251399956620585118827193400000000000000)
      constant := (54660010605394858077701817240286042310012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree048.table
  base := (-813837536429597064447477380379996829587/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-899244061057541852477470445030000000000000)
      constant := (3650832340959844490839307884503206214009480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11811626494476358809/6250000000000000000)
  centralHi := (37797204782324348189/20000000000000000000)
  directionLo := (95492965855137201461/50000000000000000000)
  directionHi := (190985931710274402923/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree049.table
  base := (-6579084039329952931699618857189521028361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-14565040596079287665842727320000000000000)
      constant := (57974014227108360256737816501241915886556) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree049.table
  base := (-1316454200972168727736465012796239024583/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (494)
      previous := (171)
      next := (0)
      square := (5488711190527294572771843600000000000000)
      linear := (-131286203049062873277064154570000000000000)
      constant := (552438884639949389563869080406658170697975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95492965855137201461/50000000000000000000)
  centralHi := (190985931710274402923/100000000000000000000)
  directionLo := (12060319587351701083/6250000000000000000)
  directionHi := (192965113397627217329/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree050.table
  base := (-332453478106383717386950445984354628527/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-14878681235537990212858261240000000000000)
      constant := (61374537364869634327417879821251629717840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree050.table
  base := (-1662966809684944188805123915722554676691/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-938762781629338373401427718950000000000000)
      constant := (4088876769847235775924773069091896416842820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12060319587351701083/6250000000000000000)
  centralHi := (192965113397627217329/100000000000000000000)
  directionLo := (6091381259638094593/3125000000000000000)
  directionHi := (194924200308419026977/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree051.table
  base := (-6717076279699862147457573714913973707747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-15192321874996692759873795160000000000000)
      constant := (64861385883397718500135127690344105169012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree051.table
  base := (-268781254280713280940536388941803245261/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-958522141915236633863406355910000000000000)
      constant := (4316235693896271878984202076713455122776375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6091381259638094593/3125000000000000000)
  centralHi := (194924200308419026977/100000000000000000000)
  directionLo := (98431896181057842071/50000000000000000000)
  directionHi := (196863792362115684143/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree052.table
  base := (-1695786506838566681050921951409044179839/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-15505962514455395306889329080000000000000)
      constant := (68434392441461611201496061857455293122576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree052.table
  base := (-6785299723617779163913198005899759902567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-978281502201134894325384992870000000000000)
      constant := (4549140055465675454639098549522558823871085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98431896181057842071/50000000000000000000)
  centralHi := (196863792362115684143/100000000000000000000)
  directionLo := (39756892041763893827/20000000000000000000)
  directionHi := (12424028763051216821/6250000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree053.table
  base := (-3423657437814531551308158576235570551887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-15819603153914097853904863000000000000000)
      constant := (72093412756908612332944818480115435584904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree053.table
  base := (-6849203560108893558278589419725927859357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-998040862487033154787363629830000000000000)
      constant := (4787582205270974034334073904625147674457535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39756892041763893827/20000000000000000000)
  centralHi := (12424028763051216821/6250000000000000000)
  directionLo := (100343373595157323857/50000000000000000000)
  directionHi := (40137349438062929543/20000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree054.table
  base := (-1381922786470999841077509067618974568893/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-16133243793372800400920396920000000000000)
      constant := (75838322398415730203713063227620508622140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree054.table
  base := (-138225393592053196416808830899427165563/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1017800222772931415249342266790000000000000)
      constant := (5031555574099853887582568034934017221853250) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100343373595157323857/50000000000000000000)
  centralHi := (40137349438062929543/20000000000000000000)
  directionLo := (202571171135348865649/100000000000000000000)
  directionHi := (4051423422706977313/2000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree055.table
  base := (-6970070031958604918370812377896424998411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-16446884432831502947935930840000000000000)
      constant := (79669014028276845270387036038414300006356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree055.table
  base := (-6971521115012217657623918882851311582749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1037559583058829675711320903750000000000000)
      constant := (5281054518888595786408415637651428662226495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202571171135348865649/100000000000000000000)
  centralHi := (4051423422706977313/2000000000000000000)
  directionLo := (51109556501490214653/25000000000000000000)
  directionHi := (204438226005960858613/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree056.table
  base := (-7028706328124869690630567346361756574283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-16760525072290205494951464760000000000000)
      constant := (83585395031751999736708940614552973702868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree056.table
  base := (-3514988828543083124537841599286935917021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (494)
      previous := (171)
      next := (0)
      square := (5488711190527294572771843600000000000000)
      linear := (-151045563334961133739042791530000000000000)
      constant := (790867741557684704514597797185914485808530) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51109556501490214653/25000000000000000000)
  centralHi := (204438226005960858613/100000000000000000000)
  directionLo := (6446511981552706427/3125000000000000000)
  directionHi := (41257676681937321133/20000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree057.table
  base := (-7085542803569764284282756764510158102627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-17074165711748908041966998680000000000000)
      constant := (87587385477977310554214990871959367589492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree057.table
  base := (-7086656315328240548989219885762208815417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1077078303630626196635278177670000000000000)
      constant := (5796610422817030259484470941446258840222835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6446511981552706427/3125000000000000000)
  centralHi := (41257676681937321133/20000000000000000000)
  directionLo := (41624418798152315963/20000000000000000000)
  directionHi := (26015261748845197477/12500000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree058.table
  base := (-7140596708668106873103445780428056300399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-17387806351207610588982532600000000000000)
      constant := (91674916365453505027800926218287774798404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree058.table
  base := (-1785392928242718894218416598996381277589/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1096837663916524457097256814630000000000000)
      constant := (6062659631936361190275536045451546347962780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41624418798152315963/20000000000000000000)
  centralHi := (26015261748845197477/12500000000000000000)
  directionLo := (104969894355973478061/50000000000000000000)
  directionHi := (209939788711946956123/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree059.table
  base := (-3596941469490659774158920173117504958337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-17701446990666313135998066520000000000000)
      constant := (95847928111934894792565922845059960333304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree059.table
  base := (-3597368212762365503111632360028259927547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1116597024202422717559235451590000000000000)
      constant := (6334218737261674103969290604568152635501970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104969894355973478061/50000000000000000000)
  centralHi := (209939788711946956123/100000000000000000000)
  directionLo := (42348376007461945583/20000000000000000000)
  directionHi := (52935470009327431979/25000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree060.table
  base := (-724541436028380243454780089389574806777/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-18015087630125015683013600440000000000000)
      constant := (100106369254323879350022539024417007728920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree060.table
  base := (-1811540317757498562236603096704761966759/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1136356384488320978021214088550000000000000)
      constant := (6611285088373123084648177224229333272576180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42348376007461945583/20000000000000000000)
  centralHi := (52935470009327431979/25000000000000000000)
  directionLo := (106764381512576558771/50000000000000000000)
  directionHi := (213528763025153117543/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree061.table
  base := (-91190026105695309203318901844973197649/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-18328728269583718230029134360000000000000)
      constant := (104450195329100181882282035859608576752320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree061.table
  base := (-3647927779474547525824343725172190113443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1156115744774219238483192725510000000000000)
      constant := (6893856404452412844393829281187626844412930) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106764381512576558771/50000000000000000000)
  centralHi := (213528763025153117543/100000000000000000000)
  directionLo := (53825204084825313853/25000000000000000000)
  directionHi := (215300816339301255413/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree062.table
  base := (-3671627865279751112636718234808472852201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-18642368909042420777044668280000000000000)
      constant := (108879367908012939302134563901532217182392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree062.table
  base := (-917978412953928654177859932816201468453/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1175875105060117498945171362470000000000000)
      constant := (7181930721983941407528513335228245121832120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53825204084825313853/25000000000000000000)
  centralHi := (215300816339301255413/100000000000000000000)
  directionLo := (217058403186071245273/100000000000000000000)
  directionHi := (108529201593035622637/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree063.table
  base := (-7389583592523692255703814809997150502227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-18956009548501123324060202200000000000000)
      constant := (113393853767349122193051159350011397991092) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree063.table
  base := (-1847520851855339595448421620900791081589/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (494)
      previous := (171)
      next := (0)
      square := (5488711190527294572771843600000000000000)
      linear := (-170804923620859394201021428490000000000000)
      constant := (1067929478556191455015525480227889248577540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217058403186071245273/100000000000000000000)
  centralHi := (108529201593035622637/50000000000000000000)
  directionLo := (218801872183499830781/100000000000000000000)
  directionHi := (109400936091749915391/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree064.table
  base := (-1858548214521539675333164524281271639663/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-19269650187959825871075736120000000000000)
      constant := (117993624172156875059927778491499653765392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree064.table
  base := (-1486925963549634398318847977657038886867/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1215393825631914019869128636390000000000000)
      constant := (7774581831060433250900207173482127363587925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218801872183499830781/100000000000000000000)
  centralHi := (109400936091749915391/50000000000000000000)
  directionLo := (55132889542179204951/25000000000000000000)
  directionHi := (44106311633743363961/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree065.table
  base := (-3738544871499785856237123090762412635259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-19583290827418528418091270040000000000000)
      constant := (122678654259425517301507301923900698917928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree065.table
  base := (-1869367915477903779606874573746928102743/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1235153185917812280331107273350000000000000)
      constant := (8079155909296783066280374909378010459311860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55132889542179204951/25000000000000000000)
  centralHi := (44106311633743363961/20000000000000000000)
  directionLo := (222247782948761186463/100000000000000000000)
  directionHi := (6945243217148787077/3125000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree066.table
  base := (-7518279627934950492857359972835283633277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-19896931466877230965106803960000000000000)
      constant := (127448922506470972102874606008658865466892) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree066.table
  base := (-3759306681371402961448648528187349704189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1254912546203710540793085910310000000000000)
      constant := (8389227501008765681901241907880198644947390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222247782948761186463/100000000000000000000)
  centralHi := (6945243217148787077/3125000000000000000)
  directionLo := (223950855999608085589/100000000000000000000)
  directionHi := (22395085599960808559/10000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree067.table
  base := (-7557767173040148322419019760986112581519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-20210572106335933512122337880000000000000)
      constant := (132304410272701826344281609586055549673924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree067.table
  base := (-7558058737864243416102425624282009384087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1274671906489608801255064547270000000000000)
      constant := (8704795670878868840043604753288907700898685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223950855999608085589/100000000000000000000)
  centralHi := (22395085599960808559/10000000000000000000)
  directionLo := (14102567194856692639/6250000000000000000)
  directionHi := (9025643004708283289/4000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree068.table
  base := (-949444552087022479558593691373025648017/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-20524212745794636059137871800000000000000)
      constant := (137245101404594021484490216716063179263456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree068.table
  base := (-1898952771220651123800322785303432332497/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1294431266775507061717043184230000000000000)
      constant := (9025859610993456700903653695690636314152940) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14102567194856692639/6250000000000000000)
  centralHi := (9025643004708283289/4000000000000000000)
  directionLo := (227318727027916165559/100000000000000000000)
  directionHi := (5682968175697904139/2500000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree069.table
  base := (-1907912715164913695017420122775124802073/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-20837853385253338606153405720000000000000)
      constant := (142270981895121118543247902565598003166832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree069.table
  base := (-3815936627257195008224056450751074463873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1314190627061405322179021821190000000000000)
      constant := (9352418622926986554699105007973973512702230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227318727027916165559/100000000000000000000)
  centralHi := (5682968175697904139/2500000000000000000)
  directionLo := (114492043975673039691/50000000000000000000)
  directionHi := (228984087951346079383/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree070.table
  base := (-3833026771737432504058583144937925631777/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-21151494024712041153168939640000000000000)
      constant := (147382039590105950100973252540496594945784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree070.table
  base := (-7666247713358925928262165711613776364113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (494)
      previous := (171)
      next := (0)
      square := (5488711190527294572771843600000000000000)
      linear := (-190564283906757654663000065450000000000000)
      constant := (1383496014623231934866748051793517827256045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114492043975673039691/50000000000000000000)
  centralHi := (228984087951346079383/100000000000000000000)
  directionLo := (57659356034074887381/25000000000000000000)
  directionHi := (9225496965451981981/4000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree071.table
  base := (-7698767103777189034280862833330295780581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-21465134664170743700184473560000000000000)
      constant := (152578263935007002102987643016678816877676) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree071.table
  base := (-962367074723591157193740390515624958537/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1353709347633201843102979095110000000000000)
      constant := (10022019525889100997415961739051375081267480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57659356034074887381/25000000000000000000)
  centralHi := (9225496965451981981/4000000000000000000)
  directionLo := (14517437022199704457/6250000000000000000)
  directionHi := (232278992355195271313/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree072.table
  base := (-120778028670067357988537356658096362907/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-21778775303629446247200007480000000000000)
      constant := (157859645756553538338468591175527331095808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree072.table
  base := (-386497088010891685476775280977826402253/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1373468707919100103564957732070000000000000)
      constant := (10365060439664980656965371619736650628960300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14517437022199704457/6250000000000000000)
  centralHi := (232278992355195271313/100000000000000000000)
  directionLo := (233909040370102832371/100000000000000000000)
  directionHi := (58477260092525708093/25000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree073.table
  base := (-3879567865939038002223384209869371463137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-22092415943088148794215541400000000000000)
      constant := (163226177074418177345924024411045028294904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree073.table
  base := (-1939816202207311955427596428038737401759/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1393228068204998364026936369030000000000000)
      constant := (10713594449685425431030055238620037346276180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233909040370102832371/100000000000000000000)
  centralHi := (58477260092525708093/25000000000000000000)
  directionLo := (235527807369278436683/100000000000000000000)
  directionHi := (58881951842319609171/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree074.table
  base := (-1557358906442632885298916154476072829843/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-22406056582546851341231075320000000000000)
      constant := (168677850938782198674663602090478543403140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree074.table
  base := (-7786907141688953721122267140074044076067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1412987428490896624488915005990000000000000)
      constant := (11067621213424269698483325179853859201363585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235527807369278436683/100000000000000000000)
  centralHi := (58881951842319609171/25000000000000000000)
  directionLo := (59283881094219796761/25000000000000000000)
  directionHi := (47427104875375837409/20000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree075.table
  base := (-156255435014906764544300493961508640871/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-22719697222005553888246609240000000000000)
      constant := (174214661290222554125466536957698271825800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree075.table
  base := (-781286997604204748937122554707928267789/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1432746788776794884950893642950000000000000)
      constant := (11427140432656464919333162910715575743916950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59283881094219796761/25000000000000000000)
  centralHi := (47427104875375837409/20000000000000000000)
  directionLo := (59683103659460750913/25000000000000000000)
  directionHi := (238732414637843003653/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree076.table
  base := (-3918534354974272204954556792529336825791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-23033337861464256435262143160000000000000)
      constant := (179836602838843455685128775459765305393672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree076.table
  base := (-3918577186736807424963939586764907745621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1452506149062693145412872279910000000000000)
      constant := (11792151847293665091329266962317195204645710) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59683103659460750913/25000000000000000000)
  centralHi := (238732414637843003653/100000000000000000000)
  directionLo := (240318693979749585611/100000000000000000000)
  directionHi := (60079673494937396403/25000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree077.table
  base := (-1571937313196766675524120115216099909997/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-23346978500922958982277677080000000000000)
      constant := (185543670960000701741475305025678001800060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree077.table
  base := (-7859761261520030204377793125992133380059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (494)
      previous := (171)
      next := (0)
      square := (5488711190527294572771843600000000000000)
      linear := (-210323644192655915124978702410000000000000)
      constant := (1737522175727065498011881983364275331697935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240318693979749585611/100000000000000000000)
  centralHi := (60079673494937396403/25000000000000000000)
  directionLo := (24189457115332304003/10000000000000000000)
  directionHi := (241894571153323040031/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree078.table
  base := (-7880626331191481006589124330784911292383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-23660619140381661529293211000000000000000)
      constant := (191335861604333188789547571016860354830468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree078.table
  base := (-394034572611662815661694844310544702233/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1492024869634489666336829553830000000000000)
      constant := (12538650382091114227269215951386330959058300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24189457115332304003/10000000000000000000)
  centralHi := (241894571153323040031/100000000000000000000)
  directionLo := (243460248153097051537/100000000000000000000)
  directionHi := (121730124076548525769/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree079.table
  base := (-7899888893498822109844660142591300513821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-23974259779840364076308744920000000000000)
      constant := (197213171220131577577225672259634797944716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree079.table
  base := (-7899945658129433116688261699295452484993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1511784229920387926798808190790000000000000)
      constant := (12920137128732178029540335710774614141176715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243460248153097051537/100000000000000000000)
  centralHi := (121730124076548525769/50000000000000000000)
  directionLo := (49003184103927422067/20000000000000000000)
  directionHi := (3828373758119329849/1562500000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree080.table
  base := (-1583495006633668909428538176041307083201/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-24287900419299066623324278840000000000000)
      constant := (203175596686345916665487677279173858335980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree080.table
  base := (-1583504901178377770711541997663958017411/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1531543590206286187260786827750000000000000)
      constant := (13307115316475234474386411668061651428671525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49003184103927422067/20000000000000000000)
  centralHi := (3828373758119329849/1562500000000000000)
  directionLo := (9862471104983996889/4000000000000000000)
  directionHi := (123280888812299961113/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree081.table
  base := (-7933385437252036722034975448440247294443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-24601541058757769170339812760000000000000)
      constant := (209223135254768252440126550456239010822228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree081.table
  base := (-7933428548146239210685279885064200475517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1551302950492184447722765464710000000000000)
      constant := (13699584809927007718530899480961270883498335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9862471104983996889/4000000000000000000)
  centralHi := (123280888812299961113/50000000000000000000)
  directionLo := (248098002939806422279/100000000000000000000)
  directionHi := (6202450073495160557/2500000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree082.table
  base := (-3973810356033760078810074905471150476881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-24915181698216471717355346680000000000000)
      constant := (215355784500128098808747747936230796184952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree082.table
  base := (-49672864209876391791166653991647119183/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1571062310778082708184744101670000000000000)
      constant := (14097545489359001829837454303435432928026400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248098002939806422279/100000000000000000000)
  centralHi := (6202450073495160557/2500000000000000000)
  directionLo := (24962477429141068617/10000000000000000000)
  directionHi := (249624774291410686171/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree083.table
  base := (-7960181393968009714422295049843059427947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-25228822337675174264370880600000000000000)
      constant := (221573542277012596329254945390627762288212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree083.table
  base := (-318408564625691681653767008244087483057/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1590821671063980968646722738630000000000000)
      constant := (14500997248576345882085909951022964166275875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24962477429141068617/10000000000000000000)
  centralHi := (249624774291410686171/100000000000000000000)
  directionLo := (25114226410016148997/10000000000000000000)
  directionHi := (251142264100161489971/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree084.table
  base := (-1992766989660165066019478039877978823871/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-25542462977133876811386414520000000000000)
      constant := (227876406682673125515102138841952338818064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree084.table
  base := (-3985548230009916857055993177802831170999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (494)
      previous := (171)
      next := (0)
      square := (5488711190527294572771843600000000000000)
      linear := (-230083004478554175586957339370000000000000)
      constant := (2129991427583661456811927657929801818030070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25114226410016148997/10000000000000000000)
  centralHi := (251142264100161489971/100000000000000000000)
  directionLo := (252650639608675433903/100000000000000000000)
  directionHi := (15790664975542214619/6250000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree085.table
  base := (-7980280829135548516649307022763349303801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-25856103616592579358401948440000000000000)
      constant := (234264376024909379526040104758946602784796) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree085.table
  base := (-7980305651069440339785000686255867289397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1630340391635777489570680012550000000000000)
      constant := (15324373638519489581080954130117312514097735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252650639608675433903/100000000000000000000)
  centralHi := (15790664975542214619/6250000000000000000)
  directionLo := (15884378943535602513/6250000000000000000)
  directionHi := (254150063096569640209/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree086.table
  base := (-7987820382799686272854677844990364252331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-26169744256051281905417482360000000000000)
      constant := (240737448794333311159196050320038542990676) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree086.table
  base := (-1597568399469449611574236333442101783681/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1650099751921675750032658649510000000000000)
      constant := (15744298109281670678098840474905425314990775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15884378943535602513/6250000000000000000)
  centralHi := (254150063096569640209/100000000000000000000)
  directionLo := (51128138416847473787/20000000000000000000)
  directionHi := (31955086510529671117/12500000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree087.table
  base := (-7993686957266450218320390660480517925537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-26483384895509984452433016280000000000000)
      constant := (247295623640411413672064511388077928297852) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree087.table
  base := (-1598741155273279487998300321034257413447/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1669859112207574010494637286470000000000000)
      constant := (16169713337381454048690014424731034668527425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51128138416847473787/20000000000000000000)
  centralHi := (31955086510529671117/12500000000000000000)
  directionLo := (64280669881497713291/25000000000000000000)
  directionHi := (51424535905198170633/20000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree088.table
  base := (-199947021390752816437333626631413087547/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-26797025534968686999448550200000000000000)
      constant := (253938899350766597846857889578973905992480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree088.table
  base := (-199947430967267334411624620409472066491/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1689618472493472270956615923430000000000000)
      constant := (16600619261430707494726315022115173748388200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64280669881497713291/25000000000000000000)
  centralHi := (51424535905198170633/20000000000000000000)
  directionLo := (258596173993241688781/100000000000000000000)
  directionHi := (129298086996620844391/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree089.table
  base := (-8000402350917310075887067446964304591791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-27110666174427389546464084120000000000000)
      constant := (260667274833292317741522079342142781632836) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree089.table
  base := (-800041661145810384637342172409364331789/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1709377832779370531418594560390000000000000)
      constant := (17037015825780628861332703613359057387116950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258596173993241688781/100000000000000000000)
  centralHi := (129298086996620844391/50000000000000000000)
  directionLo := (260061319848339734673/100000000000000000000)
  directionHi := (130030659924169867337/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree090.table
  base := (-8001251689951898238194978393575062141299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-27424306813886092093479618040000000000000)
      constant := (267480749100693150297283398325699751434804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree090.table
  base := (-4000632050707244367697034542864859342299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1729137193065268791880573197350000000000000)
      constant := (17478902979778482476518252292896218922273490) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260061319848339734673/100000000000000000000)
  centralHi := (130030659924169867337/50000000000000000000)
  directionLo := (16344891088102890623/6250000000000000000)
  directionHi := (261518257409646249969/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree091.table
  base := (-8000429096696374312935564365837391364287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-27737947453344794640495151960000000000000)
      constant := (274379321257119106840067900686650434542852) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree091.table
  base := (-8000439897526577698254183252753450399129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (494)
      previous := (171)
      next := (0)
      square := (5488711190527294572771843600000000000000)
      linear := (-249842364764452436048935976330000000000000)
      constant := (2560897239589631367839254750659629236030485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16344891088102890623/6250000000000000000)
  centralHi := (261518257409646249969/100000000000000000000)
  directionLo := (262967123108375524947/100000000000000000000)
  directionHi := (65741780777093881237/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree092.table
  base := (-319917391005664233397002773470957814059/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-28051588092803497187510685880000000000000)
      constant := (281362990486606717230610610532904218594100) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree092.table
  base := (-159958883464669089119033935964464023371/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1768655913637065312804530471270000000000000)
      constant := (18379148875334864644757803018123315713705250) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262967123108375524947/100000000000000000000)
  centralHi := (65741780777093881237/25000000000000000000)
  directionLo := (264408049637701201163/100000000000000000000)
  directionHi := (66102012409425300291/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree093.table
  base := (-3996884455903370583414891573663962940843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-28365228732262199734526219800000000000000)
      constant := (288431756043079388018246368500688296473256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree093.table
  base := (-3996888544193712800964568267657479565617/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1788415273922963573266509108230000000000000)
      constant := (18837507535237002570773892514185835012847670) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264408049637701201163/100000000000000000000)
  centralHi := (66102012409425300291/25000000000000000000)
  directionLo := (265841166094588509991/100000000000000000000)
  directionHi := (33230145761823563749/12500000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree094.table
  base := (-7987931677902669303832909840297086996693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-28678869371720902281541753720000000000000)
      constant := (295585617241693563222242358418811652013228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree094.table
  base := (-7987938790927959085286005843176542709257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1808174634208861833728487745190000000000000)
      constant := (19301356620588663705393673414913747036232035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (265841166094588509991/100000000000000000000)
  centralHi := (33230145761823563749/12500000000000000000)
  directionLo := (267266598114781505271/100000000000000000000)
  directionHi := (33408324764347688159/12500000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree095.table
  base := (-7980423231205061172420007052154794390781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-28992510011179604828557287640000000000000)
      constant := (302824573451346559136656349741380822436876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree095.table
  base := (-99755367729077536827278972184399369809/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1827933994494760094190466382150000000000000)
      constant := (19770696097709416778777942522335772351743600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267266598114781505271/100000000000000000000)
  centralHi := (33408324764347688159/12500000000000000000)
  directionLo := (53736893600268954197/20000000000000000000)
  directionHi := (134342234000672385493/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree096.table
  base := (-996405464709587329170734628371250314839/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-29306150650638307375572821560000000000000)
      constant := (310148624088187248318389133492119989925152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree096.table
  base := (-7971249098832294338920358383658091751689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1847693354780658354652445019110000000000000)
      constant := (20245525935177978188122639753315767520836195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53736893600268954197/20000000000000000000)
  centralHi := (134342234000672385493/50000000000000000000)
  directionLo := (54018978969426364173/20000000000000000000)
  directionHi := (135047447423565910433/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree097.table
  base := (-3980196636436671049990587536455883625767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-29619791290097009922588355480000000000000)
      constant := (317557768609992589114198088438352930993864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree097.table
  base := (-3980198976276559291482237081610171521369/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1867452715066556615114423656070000000000000)
      constant := (20725846103568161030159000216989015954529190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54018978969426364173/20000000000000000000)
  centralHi := (135047447423565910433/50000000000000000000)
  directionLo := (135748997325763633727/50000000000000000000)
  directionHi := (54299598930305453491/20000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree098.table
  base := (-3973936011581341550201320354100312950479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-29933431929555712469603889400000000000000)
      constant := (325052006511291815411536256507197496396168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree098.table
  base := (-7947876092384271671319415507977657078773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (494)
      previous := (171)
      next := (0)
      square := (5488711190527294572771843600000000000000)
      linear := (-269601725050350696510914613290000000000000)
      constant := (3030236653602934898085837152384782002242945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135748997325763633727/50000000000000000000)
  centralHi := (54299598930305453491/20000000000000000000)
  directionLo := (136446940215893318883/50000000000000000000)
  directionHi := (272893880431786637767/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree099.table
  base := (-3966840043390935428039865902699078695889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-30247072569014415016619423320000000000000)
      constant := (332631337319136330324605806208407370432888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree099.table
  base := (-3966841812408313068733114726922377555541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1906971435638353136038380929990000000000000)
      constant := (21702957324044864186745362778630034997784910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136446940215893318883/50000000000000000000)
  centralHi := (272893880431786637767/100000000000000000000)
  directionLo := (274282662329276283581/100000000000000000000)
  directionHi := (137141331164638141791/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree100.table
  base := (-7917817574755602877649928555602156002327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-30560713208473117563634957240000000000000)
      constant := (340295760589427343810856816777591375990692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree100.table
  base := (-7917820650635021157236667919955904538807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1926730795924251396500359566950000000000000)
      constant := (22199748325348835132513729132610803387992285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274282662329276283581/100000000000000000000)
  centralHi := (137141331164638141791/50000000000000000000)
  directionLo := (55132889542179204951/20000000000000000000)
  directionHi := (68916111927724006189/25000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree101.table
  base := (-7900284591693751838395406914767723548703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-30874353847931820110650491160000000000000)
      constant := (348045275903725365177160584390929105805188) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree101.table
  base := (-7900287265524126051588034766746425172407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1946490156210149656962338203910000000000000)
      constant := (22702029555689713140271419682829125832760285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55132889542179204951/20000000000000000000)
  centralHi := (68916111927724006189/25000000000000000000)
  directionLo := (138519670632974418241/50000000000000000000)
  directionHi := (277039341265948836483/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree102.table
  base := (-197027030912122457696961294969255445993/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-31187994487390522657666025080000000000000)
      constant := (355879882866476072145267969384919128641120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree102.table
  base := (-1576216712118880857784542024002399024889/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1966249516496047917424316840870000000000000)
      constant := (23209800992745434660259851298465061194510975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138519670632974418241/50000000000000000000)
  centralHi := (277039341265948836483/100000000000000000000)
  directionLo := (139203722549352460873/50000000000000000000)
  directionHi := (278407445098704921747/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree103.table
  base := (-7860207602899894176529176006991209889431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-31501635126849225204681559000000000000000)
      constant := (363799581102596057153458520562035160442276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree103.table
  base := (-3930104811419641579506034824167878655333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-1986008876781946177886295477830000000000000)
      constant := (23723062615202610006485036940715739458886830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139203722549352460873/50000000000000000000)
  centralHi := (278407445098704921747/100000000000000000000)
  directionLo := (8742776838027868291/3125000000000000000)
  directionHi := (279768858816891785313/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree104.table
  base := (-3918831890058822754215218341439093965099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-31815275766307927751697092920000000000000)
      constant := (371804370255369695945400809348487248279208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree104.table
  base := (-979708191941633751698906889489540014121/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2005768237067844438348274114790000000000000)
      constant := (24241814402659033877771866877352501572322840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8742776838027868291/3125000000000000000)
  centralHi := (279768858816891785313/100000000000000000000)
  directionLo := (35140459952040917893/12500000000000000000)
  directionHi := (56224735923265468629/20000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree105.table
  base := (-3906724926591816820978397557028624005413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-32128916405766630298712626840000000000000)
      constant := (379894249984615063167596590593771007956696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree105.table
  base := (-976681422322226608472305912318194789231/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (494)
      previous := (171)
      next := (0)
      square := (5488711190527294572771843600000000000000)
      linear := (-289361085336248956972893250250000000000000)
      constant := (3538008047934100644345198116900905459015320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35140459952040917893/12500000000000000000)
  centralHi := (56224735923265468629/20000000000000000000)
  directionLo := (282472002361899567803/100000000000000000000)
  directionHi := (70618000590474891951/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree106.table
  base := (-1946891475852563246073598647452387255577/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-32442557045225332845728160760000000000000)
      constant := (388069219965082581191301291140761803910768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree106.table
  base := (-1946891807201537480892008818049304191403/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2045286957639640959272231388710000000000000)
      constant := (25295788395017625544929971439963681892425060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282472002361899567803/100000000000000000000)
  centralHi := (70618000590474891951/25000000000000000000)
  directionLo := (283813919665083601581/100000000000000000000)
  directionHi := (141906959832541800791/50000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree107.table
  base := (-7760012008726801528005324402960742545457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-32756197684684035392743694680000000000000)
      constant := (396329279885055058046266553818157029818172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree107.table
  base := (-7760013160246202336931612717274453810309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2065046317925539219734210025670000000000000)
      constant := (25831010562958907298099580290625758816474295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (283813919665083601581/100000000000000000000)
  centralHi := (141906959832541800791/50000000000000000000)
  directionLo := (285149521958175587581/100000000000000000000)
  directionHi := (142574760979087793791/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree108.table
  base := (-7730788243985888416899252644144018765091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-33069838324142737939759228600000000000000)
      constant := (404674429445122057157253706263423924939636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree108.table
  base := (-7730789244353714234478925278264116303153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2084805678211437480196188662630000000000000)
      constant := (26371722821855892458905825687393291505727515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (285149521958175587581/100000000000000000000)
  centralHi := (142574760979087793791/50000000000000000000)
  directionLo := (286478897565411604383/100000000000000000000)
  directionHi := (8952465548919112637/3125000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree109.table
  base := (-1539978936246419683128225079592769046921/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-33383478963601440486774762520000000000000)
      constant := (413104668357105239465602964138144619061580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree109.table
  base := (-7699895550215913791502014890942992454757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2104565038497335740658167299590000000000000)
      constant := (26917925154782210124402157356000966848584535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286478897565411604383/100000000000000000000)
  centralHi := (8952465548919112637/3125000000000000000)
  directionLo := (287802132771129978217/100000000000000000000)
  directionHi := (143901066385564989109/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree110.table
  base := (-7667331389937955637439675336880212663983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-33697119603060143033790296440000000000000)
      constant := (421619996343114508518479396752479149344068) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree110.table
  base := (-3833666072365471055893226833252167373783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2124324398783234001120145936550000000000000)
      constant := (27469617545347815724161110129206437986846330) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287802132771129978217/100000000000000000000)
  centralHi := (143901066385564989109/50000000000000000000)
  directionLo := (289119311885125828999/100000000000000000000)
  directionHi := (289119311885125829/100000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree111.table
  base := (-238534326162860652808861748122562863497/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-34010760242518845580805830360000000000000)
      constant := (430220413134717541085528310190311953472384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree111.table
  base := (-1526619818553231621800001277671636209803/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2144083759069132261582124573510000000000000)
      constant := (28026799977660206324334081635074245642991325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289119311885125828999/100000000000000000000)
  centralHi := (289119311885125829/100000000000000000)
  directionLo := (290430517305337929817/100000000000000000000)
  directionHi := (145215258652668964909/50000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree112.table
  base := (-7597195887979523447613363726564148300851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-34324400881977548127821364280000000000000)
      constant := (438905918472207660068187558373743406796596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree112.table
  base := (-1519439291459633010731282437483620221469/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (494)
      previous := (171)
      next := (0)
      square := (5488711190527294572771843600000000000000)
      linear := (-309120445622147217434871887210000000000000)
      constant := (4084210348041444874806457969504366461242925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290430517305337929817/100000000000000000000)
  centralHi := (145215258652668964909/50000000000000000000)
  directionLo := (466777327324799639/160000000000000000)
  directionHi := (36466978697249971797/12500000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree113.table
  base := (-302384952205954238505528396333098228069/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-34638041521436250674836898200000000000000)
      constant := (447676512103957054858420456456690177193100) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree113.table
  base := (-7559624299537007166179453907307402130899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2183602479640928782506081847430000000000000)
      constant := (29157634906241078288090655786887686477929745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466777327324799639/160000000000000000)
  centralHi := (36466978697249971797/12500000000000000000)
  directionLo := (293035327455379108763/100000000000000000000)
  directionHi := (73258831863844777191/25000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree114.table
  base := (-7520382249749939376924344377995203647759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-34951682160894953221852432120000000000000)
      constant := (456532193785844121688362084868019185408964) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree114.table
  base := (-7520382679036643375139832576843276548839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2203361839926827042968060484390000000000000)
      constant := (29731287372922378880170609884085397245534445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (293035327455379108763/100000000000000000000)
  centralHi := (73258831863844777191/25000000000000000000)
  directionLo := (147164543975611525849/50000000000000000000)
  directionHi := (294329087951223051699/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree115.table
  base := (-747947128106368344726314330101974618081/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-35265322800353655768867966040000000000000)
      constant := (465472963280745221530846938945921015276760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree115.table
  base := (-7479471653793512196733692780460695249119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2223121200212725303430039121350000000000000)
      constant := (30310429822124888463417012654937129663965845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147164543975611525849/50000000000000000000)
  centralHi := (294329087951223051699/100000000000000000000)
  directionLo := (36952148299252407917/12500000000000000000)
  directionHi := (295617186394019263337/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree116.table
  base := (-7436890956734559498756609089856158372609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-35578963439812358315883499960000000000000)
      constant := (474498820358082469085467009040575366509564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree116.table
  base := (-7436891280334749825248999262329140567917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2242880560498623563892017758310000000000000)
      constant := (30895062239999458670229312737121360560860335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36952148299252407917/12500000000000000000)
  centralHi := (295617186394019263337/100000000000000000000)
  directionLo := (296899696478177392487/100000000000000000000)
  directionHi := (37112462059772174061/12500000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree117.table
  base := (-739264133287145810611316890406589125003/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-35892604079271060862899033880000000000000)
      constant := (483609764793420302053388586513736434999880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree117.table
  base := (-3696320806898703557756958846989635145647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2262639920784521824353996395270000000000000)
      constant := (31485184613037512041174609541113078778632970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (296899696478177392487/100000000000000000000)
  centralHi := (37112462059772174061/12500000000000000000)
  directionLo := (298176690313229203703/100000000000000000000)
  directionHi := (37272086289153650463/12500000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree118.table
  base := (-3673361232068959682870353651144410425973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-36206244718729763409914567800000000000000)
      constant := (492805796368104560048980133130844716592216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree118.table
  base := (-3673361353999912587401883484431660732811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2282399281070420084815975032230000000000000)
      constant := (32080796928053555004970449938016486240922610) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298176690313229203703/100000000000000000000)
  centralHi := (37272086289153650463/12500000000000000000)
  directionLo := (149724119235570165139/50000000000000000000)
  directionHi := (299448238471140330279/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree119.table
  base := (-7299134403833091922991179291543632234703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-36519885358188465956930101720000000000000)
      constant := (502086914868938648490833828863825471061188) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree119.table
  base := (-7299134615506169460272955635229674591287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (494)
      previous := (171)
      next := (0)
      square := (5488711190527294572771843600000000000000)
      linear := (-328879805908045477896850524170000000000000)
      constant := (4668842738881338146373429119072961389304955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149724119235570165139/50000000000000000000)
  centralHi := (299448238471140330279/100000000000000000000)
  directionLo := (150357205015910744859/50000000000000000000)
  directionHi := (300714410031821489719/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree120.table
  base := (-7249877203964594349942984690864746221329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-36833525997647168503945635640000000000000)
      constant := (511453120087892093090636074436541015114684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree120.table
  base := (-1449975477536996980975726486614278165281/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2321918001642216605739932306150000000000000)
      constant := (33288491332799654591530769786297509247530775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150357205015910744859/50000000000000000000)
  centralHi := (300714410031821489719/100000000000000000000)
  directionLo := (37746909078365276277/12500000000000000000)
  directionHi := (301975272626922210217/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree121.table
  base := (-1799737728828573713889169218434119548611/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-37147166637105871050961169560000000000000)
      constant := (520904411821837421012544656355054087222224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree121.table
  base := (-3599475537381258249334129119283071417101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2341677361928114866201910943110000000000000)
      constant := (33900573397638987683159119881713295005620510) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37746909078365276277/12500000000000000000)
  centralHi := (301975272626922210217/100000000000000000000)
  directionLo := (30323089248198562723/10000000000000000000)
  directionHi := (303230892481985627231/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree122.table
  base := (-3573177793748944612325346007294158457759/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-37460807276564573597976703480000000000000)
      constant := (530440789872311849117285829921646732337928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree122.table
  base := (-3573177862935719105482437552410183394073/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2361436722214013126663889580070000000000000)
      constant := (34518145354649861177014908816747010136904230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30323089248198562723/10000000000000000000)
  centralHi := (303230892481985627231/100000000000000000000)
  directionLo := (304481334457038697587/100000000000000000000)
  directionHi := (76120333614259674397/25000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree123.table
  base := (-7092091269019039368891266995134857724577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-37774447916023276144992237400000000000000)
      constant := (540062254045300729758194647609460569101692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree123.table
  base := (-7092091389095545815153164665774576761227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2381196082499911387125868217030000000000000)
      constant := (35141207192051745108618889591083228693499385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304481334457038697587/100000000000000000000)
  centralHi := (76120333614259674397/25000000000000000000)
  directionLo := (305726662085688225237/100000000000000000000)
  directionHi := (152863331042844112619/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree124.table
  base := (-7036158007318733382585427915073997219231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-38088088555481978692007771320000000000000)
      constant := (549768804151040110558043005019704011123076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree124.table
  base := (-879519763938861758131073006814700533993/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2400955442785809647587846853990000000000000)
      constant := (35769758898311006063286275207115186953373720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (305726662085688225237/100000000000000000000)
  centralHi := (152863331042844112619/50000000000000000000)
  directionLo := (306966937612789380093/100000000000000000000)
  directionHi := (153483468806394690047/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree125.table
  base := (-218079870275638760303828064601739523359/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-38401729194940681239023305240000000000000)
      constant := (559560440003836115260873608980977341010048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree125.table
  base := (-6978555939223794047576263432135800787021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2420714803071707908049825490950000000000000)
      constant := (36403800462131597824720408775376728807179855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306966937612789380093/100000000000000000000)
  centralHi := (153483468806394690047/50000000000000000000)
  directionLo := (308202222030749902781/100000000000000000000)
  directionHi := (154101111015374951391/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree126.table
  base := (-6919284838971557250121702430080211885419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-38715369834399383786038839160000000000000)
      constant := (569437161421899155707409559579679152458324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree126.table
  base := (-3459642458703015460921124179790882352507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (494)
      previous := (171)
      next := (0)
      square := (5488711190527294572771843600000000000000)
      linear := (-348639166193943738358829161130000000000000)
      constant := (5291904553206633289848615590490638235324510) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308202222030749902781/100000000000000000000)
  centralHi := (154101111015374951391/50000000000000000000)
  directionLo := (19339535944658119281/6250000000000000000)
  directionHi := (309432575114529908497/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree127.table
  base := (-3429172511140790212995838133671261416681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-39029010473858086333054373080000000000000)
      constant := (579398968227191246768816315760629908666552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree127.table
  base := (-1371669018065522875960701670474349599879/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2460233523643504428973782764870000000000000)
      constant := (37688353118409359301416518749986921740148225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19339535944658119281/6250000000000000000)
  centralHi := (309432575114529908497/100000000000000000000)
  directionLo := (310658055455394118289/100000000000000000000)
  directionHi := (31065805545539411829/10000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree128.table
  base := (-6795736442357376385084243967495734389081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-39342651113316788880069907000000000000000)
      constant := (589445860245284922334086579970017062443676) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree128.table
  base := (-424733531336708308662201879479194678931/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2479992883929402689435761401830000000000000)
      constant := (38338864189387673455450916893049556858590480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310658055455394118289/100000000000000000000)
  centralHi := (31065805545539411829/10000000000000000000)
  directionLo := (311878720493470443161/100000000000000000000)
  directionHi := (155939360246735221581/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree129.table
  base := (-6731459141935879215955460031417236214789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-39656291752775491427085440920000000000000)
      constant := (599577837305232446048996134204331055140844) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree129.table
  base := (-6731459193141347662963454824648009180279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2499752244215300949897740038790000000000000)
      constant := (38994865074955116030180723442363237750831645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311878720493470443161/100000000000000000000)
  centralHi := (155939360246735221581/50000000000000000000)
  directionLo := (156547313274583056537/50000000000000000000)
  directionHi := (12523785061966644523/4000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree130.table
  base := (-6665513162914498485216982998603214031211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-39969932392234193974100974840000000000000)
      constant := (609794899239444179647098344305587143875156) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree130.table
  base := (-133310264146600606292516646987247564821/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2519511604501199210359718675750000000000000)
      constant := (39656355764885295943985114212106217330942750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156547313274583056537/50000000000000000000)
  centralHi := (12523785061966644523/4000000000000000000)
  directionLo := (314305828853489968421/100000000000000000000)
  directionHi := (157152914426744984211/50000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree131.table
  base := (-659789854637948547057089868082388412213/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-40283573031692896521116508760000000000000)
      constant := (620097045883575118017584867026704463511480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree131.table
  base := (-1649474646225806135866359544649350627159/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2539270964787097470821697312710000000000000)
      constant := (40323336249145501502642735696745636385384180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314305828853489968421/100000000000000000000)
  centralHi := (157152914426744984211/50000000000000000000)
  directionLo := (39439047697165888141/12500000000000000000)
  directionHi := (315512381577327105129/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree132.table
  base := (-816076916579059222005188067029505069439/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-40597213671151599068132042680000000000000)
      constant := (630484277076418726744358512535055837777952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree132.table
  base := (-652861536604408598076943805731729385631/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2559030325072995731283675949670000000000000)
      constant := (40995806517890859576488232288765263005204050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39439047697165888141/12500000000000000000)
  centralHi := (315512381577327105129/100000000000000000000)
  directionLo := (316714337859709776873/100000000000000000000)
  directionHi := (158357168929854888437/50000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree133.table
  base := (-6457663561215383003394308042058574712833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-40910854310610301615147576600000000000000)
      constant := (640956592659807327420357250921765701148668) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree133.table
  base := (-6457663590191637458284790190607558826997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (494)
      previous := (171)
      next := (0)
      square := (5488711190527294572771843600000000000000)
      linear := (-368398526479841998820807798090000000000000)
      constant := (5953395223065544224534799889702735441055105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316714337859709776873/100000000000000000000)
  centralHi := (158357168929854888437/50000000000000000000)
  directionLo := (317911749835126299967/100000000000000000000)
  directionHi := (4967371091173848437/1562500000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree134.table
  base := (-6385043270933850435119084687291021787413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-41224494950069004162163110520000000000000)
      constant := (651513992478518370915621980230835912850348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree134.table
  base := (-6385043296062158621659771288524035081811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2598549045644792252207633223590000000000000)
      constant := (42357216370363862975225008720243611404956305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (317911749835126299967/100000000000000000000)
  centralHi := (4967371091173848437/1562500000000000000)
  directionLo := (319104668659907669957/100000000000000000000)
  directionHi := (159552334329953834979/50000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree135.table
  base := (-788844312484916892273876003721159624823/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-41538135589527706709178644440000000000000)
      constant := (662156476380186020962252006230922892005664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree135.table
  base := (-3155377260834757278772757653549573773037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2618308405930690512669611860550000000000000)
      constant := (43046155935292622840702932946510708851211870) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319104668659907669957/100000000000000000000)
  centralHi := (159552334329953834979/50000000000000000000)
  directionLo := (320293144537729676313/100000000000000000000)
  directionHi := (160146572268864838157/50000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree136.table
  base := (-3117398642725010545767533606512903506121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-41851776228986409256194178360000000000000)
      constant := (672884044215217541644547372347896771951032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree136.table
  base := (-3117398652172257693924607864953864566713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2638067766216588773131590497510000000000000)
      constant := (43740585247099040688310109503244606362310630) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320293144537729676313/100000000000000000000)
  centralHi := (160146572268864838157/50000000000000000000)
  directionLo := (321477226744266485487/100000000000000000000)
  directionHi := (20092326671516655343/6250000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree137.table
  base := (-1231434332874126100102031089221784588223/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-42165416868445111803209712280000000000000)
      constant := (683696695836714044141072505745564308235540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree137.table
  base := (-6157171680753387825464562884863539420019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2657827126502487033593569134470000000000000)
      constant := (44440504296799890973387584260106432842095345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (321477226744266485487/100000000000000000000)
  centralHi := (20092326671516655343/6250000000000000000)
  directionLo := (161328481825514973261/50000000000000000000)
  directionHi := (322656963651029946523/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree138.table
  base := (-6077877672711245066792914922051081230059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-42479057507903814350225246200000000000000)
      constant := (694594431100395201645120837651795675079764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree138.table
  base := (-759734710864428774424302752153672844633/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2677586486788385294055547771430000000000000)
      constant := (45145913075570445606309655232006801224519320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161328481825514973261/50000000000000000000)
  centralHi := (322656963651029946523/100000000000000000000)
  directionLo := (323832402748427251087/100000000000000000000)
  directionHi := (20239525171776703193/6250000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree139.table
  base := (-5996915345905221353884754440281263919193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-42792698147362516897240780120000000000000)
      constant := (705577249864527587902686732868874944323228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree139.table
  base := (-5996915358219914199144207762896650693579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2697345847074283554517526408390000000000000)
      constant := (45856811574740333020207495833152320580073145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323832402748427251087/100000000000000000000)
  centralHi := (20239525171776703193/6250000000000000000)
  directionLo := (325003590668068045469/100000000000000000000)
  directionHi := (32500359066806804547/10000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree140.table
  base := (-5914284718766276287380828171659655679247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-43106338786821219444256314040000000000000)
      constant := (716645151989856335211389574713361377283012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree140.table
  base := (-2957142364721144781550359708758670951489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (494)
      previous := (171)
      next := (0)
      square := (5488711190527294572771843600000000000000)
      linear := (-388157886765740259282786435050000000000000)
      constant := (6653314255112795433159477176586893033395770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (325003590668068045469/100000000000000000000)
  centralHi := (32500359066806804547/10000000000000000000)
  directionLo := (65234114640870128089/20000000000000000000)
  directionHi := (163085286602175320223/50000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree141.table
  base := (-2914992912752405024031509338793325707497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-43419979426279921991271847960000000000000)
      constant := (727798137339539842848101832939653394340024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree141.table
  base := (-72874822934496768904044643455127414827/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2736864567646080075441483682310000000000000)
      constant := (47295077700344740261896582889521502669390800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65234114640870128089/20000000000000000000)
  centralHi := (163085286602175320223/50000000000000000000)
  directionLo := (163666697667677795439/50000000000000000000)
  directionHi := (327333395335355590879/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree142.table
  base := (-1148803739948705195276160457941193282419/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-43733620065738624538287381880000000000000)
      constant := (739036205779087297451025602221176134351620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree142.table
  base := (-5744018707766145620285422112666297312037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2756623927931978335903462319270000000000000)
      constant := (48022445310175350194047422540984757158550935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163666697667677795439/50000000000000000000)
  centralHi := (327333395335355590879/100000000000000000000)
  directionLo := (328492101243073615837/100000000000000000000)
  directionHi := (164246050621536807919/50000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree143.table
  base := (-5656383374532400454651152173518068860909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-44047260705197327085302915800000000000000)
      constant := (750359357176298793490892989895927724556364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree143.table
  base := (-5656383381486459891017299836470725298183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2776383288217876596365440956230000000000000)
      constant := (48755302607190283117581257205502672301945165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (328492101243073615837/100000000000000000000)
  centralHi := (164246050621536807919/50000000000000000000)
  directionLo := (329646734332993597567/100000000000000000000)
  directionHi := (2575365111976512481/781250000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree144.table
  base := (-2783539941181524967676584819978551379969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-44360901344656029632318449720000000000000)
      constant := (761767591401207865157787590720171588960248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree144.table
  base := (-5567079888390589837147001987320304998623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2796142648503774856827419593190000000000000)
      constant := (49493649583434412181904276534898525275337365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (329646734332993597567/100000000000000000000)
  centralHi := (2575365111976512481/781250000000000000)
  directionLo := (165398668626537614853/50000000000000000000)
  directionHi := (330797337253075229707/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree145.table
  base := (-2738054127591268612641910958025166279767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-44674541984114732179333983640000000000000)
      constant := (773260908326026261224521535785798669761864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree145.table
  base := (-1369027065101689685766700779470475232943/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2815902008789673117289398230150000000000000)
      constant := (50237486231085322682340373263768934271715860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165398668626537614853/50000000000000000000)
  centralHi := (330797337253075229707/100000000000000000000)
  directionLo := (82985987978032444479/25000000000000000000)
  directionHi := (331943951912129777917/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree146.table
  base := (-5383468524406654716912500232292229772179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-44988182623573434726349517560000000000000)
      constant := (784839307825090812121217260170831080911284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree146.table
  base := (-2691734264467206088075041885872509516863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2835661369075571377751376867110000000000000)
      constant := (50986812542450150454883069158934470336737130) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82985987978032444479/25000000000000000000)
  centralHi := (331943951912129777917/100000000000000000000)
  directionLo := (20817913718601960381/6250000000000000000)
  directionHi := (333086619497631366097/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree147.table
  base := (-5289160720932718394283188497815993359931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-45301823263032137273365051480000000000000)
      constant := (796502789774812253911698828238736026560276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree147.table
  base := (-1322290181214170767392854174266323191297/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (494)
      previous := (171)
      next := (0)
      square := (5488711190527294572771843600000000000000)
      linear := (-407917247051638519744765072010000000000000)
      constant := (7391661215708932561557799128156714753218420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20817913718601960381/6250000000000000000)
  centralHi := (333086619497631366097/100000000000000000000)
  directionLo := (334225380492980205113/100000000000000000000)
  directionHi := (167112690246490102557/50000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree148.table
  base := (-324574054696993941087201939702957458699/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-45615463902490839820380585400000000000000)
      constant := (808251354053625887395968862699010722643264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree148.table
  base := (-5193184878552441295592810429396670636091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2875180089647367898675334141030000000000000)
      constant := (52501934126179631991700755387045815694157705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334225380492980205113/100000000000000000000)
  centralHi := (167112690246490102557/50000000000000000000)
  directionLo := (167680137347119117797/50000000000000000000)
  directionHi := (67072054938847647119/20000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree149.table
  base := (-1273885254240286560519632224072739176079/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-45929104541949542367396119320000000000000)
      constant := (820085000541943962430707759344836173182736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree149.table
  base := (-2547770509953974766458460405960228167121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2894939449933266159137312777990000000000000)
      constant := (53267729383779328280989402947201488198110710) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167680137347119117797/50000000000000000000)
  centralHi := (67072054938847647119/20000000000000000000)
  directionLo := (336491341226356758667/100000000000000000000)
  directionHi := (84122835306589189667/25000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree150.table
  base := (-312264323485915356681933759640932851559/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-46242745181408244914411653240000000000000)
      constant := (832003729122109687981604085882980297500224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree150.table
  base := (-4996229178328145367232056465054495121257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2914698810219164419599291414950000000000000)
      constant := (54039014275557407090276900965561648695292035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (336491341226356758667/100000000000000000000)
  centralHi := (84122835306589189667/25000000000000000000)
  directionLo := (168809309279457388041/50000000000000000000)
  directionHi := (337618618558914776083/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree151.table
  base := (-2447624690267486533414658307832019855481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-46556385820866947461427187160000000000000)
      constant := (844007539678352777588910435087343841156152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree151.table
  base := (-2447624691373783958406648812378115403667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2934458170505062680061270051910000000000000)
      constant := (54815788794424906335585854784316723452203170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (168809309279457388041/50000000000000000000)
  centralHi := (337618618558914776083/100000000000000000000)
  directionLo := (338742144521385951149/100000000000000000000)
  directionHi := (6774842890427719023/2000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree152.table
  base := (-479260165972382413367441677159406715447/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-46870026460325650008442721080000000000000)
      constant := (856096432096746448005263772993623731382120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree152.table
  base := (-1198150415410236454094830909250108809861/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2954217530790960940523248688870000000000000)
      constant := (55598052933405517501410187963702893366336220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338742144521385951149/100000000000000000000)
  centralHi := (6774842890427719023/2000000000000000000)
  directionLo := (339861956317951332193/100000000000000000000)
  directionHi := (169930978158975666097/50000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree153.table
  base := (-2344143020686212370584502830876902663339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-47183667099784352555458255000000000000000)
      constant := (868270406265165795895773039442984778693288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree153.table
  base := (-4688286043033462097383998872110271881763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-2973976891076859200985227325830000000000000)
      constant := (56385806685633070745043703732990983388968065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (339861956317951332193/100000000000000000000)
  centralHi := (169930978158975666097/50000000000000000000)
  directionLo := (340978090541874248339/100000000000000000000)
  directionHi := (17048904527093712417/5000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree154.table
  base := (-4582302553071609255065578804164263949263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-47497307739243055102473788920000000000000)
      constant := (880529462073247483797428252363342944202948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree154.table
  base := (-2291151277255355175158871072159276378287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (494)
      previous := (171)
      next := (0)
      square := (5488711190527294572771843600000000000000)
      linear := (-427676607337536780206743708970000000000000)
      constant := (8168435720621299376688035640384850653519910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (340978090541874248339/100000000000000000000)
  centralHi := (17048904527093712417/5000000000000000000)
  directionLo := (342090583189453091407/100000000000000000000)
  directionHi := (21380661449340818213/6250000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree155.table
  base := (-4474651221981587571653099850862311720359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-47810948378701757649489322840000000000000)
      constant := (892873599412350672125073557146550753118564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree155.table
  base := (-4474651223228355525888683337999140262603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-3013495611648655721909184599750000000000000)
      constant := (57977783002900454263804333391140210635662265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342090583189453091407/100000000000000000000)
  centralHi := (21380661449340818213/6250000000000000000)
  directionLo := (171599734836783517757/50000000000000000000)
  directionHi := (68639893934713407103/20000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree156.table
  base := (-2182666037420707583215170087829487081449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-48124589018160460196504856760000000000000)
      constant := (905302818175519138976713868297364103348408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree156.table
  base := (-1091333018980377952819520784408261073949/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-3033254971934553982371163236710000000000000)
      constant := (58782005554737043650148546590631904147529980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171599734836783517757/50000000000000000000)
  centralHi := (68639893934713407103/20000000000000000000)
  directionLo := (344304784836829115753/100000000000000000000)
  directionHi := (172152392418414557877/50000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree157.table
  base := (-850869027595635929919664941367680121431/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-48438229657619162743520390680000000000000)
      constant := (917817118257444533911545086102646397571380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree157.table
  base := (-4254345138913849191333707645519751123419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-3053014332220452242833141873670000000000000)
      constant := (59591717693409564649561186386105660974762345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (344304784836829115753/100000000000000000000)
  centralHi := (172152392418414557877/50000000000000000000)
  directionLo := (345406562964360487373/100000000000000000000)
  directionHi := (172703281482180243687/50000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree158.table
  base := (-4141690437315916298745789971504196005327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-48751870297077865290535924600000000000000)
      constant := (930416499554430715819212264453983215978692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree158.table
  base := (-4141690438126439560674066272072763862669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-3072773692506350503295120510630000000000000)
      constant := (60406919412567354647860717972010172853646095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345406562964360487373/100000000000000000000)
  centralHi := (172703281482180243687/50000000000000000000)
  directionLo := (346504837796199115579/100000000000000000000)
  directionHi := (17325241889809955779/5000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree159.table
  base := (-503420999798033019590396926833427257127/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-49065510936536567837551458520000000000000)
      constant := (943100961964359128528313645571330327771936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree159.table
  base := (-4027367999086352580990407491057008924969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-3092533052792248763757099147590000000000000)
      constant := (61227610705956281577932785472273032813382595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346504837796199115579/100000000000000000000)
  centralHi := (17325241889809955779/5000000000000000000)
  directionLo := (173799821269677800873/50000000000000000000)
  directionHi := (347599642539355601747/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree160.table
  base := (-391137784632687349134673965228104204429/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-49379151575995270384566992440000000000000)
      constant := (955870505386655170967584194990875831822840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree160.table
  base := (-1955688923467505434801776672076447637609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-3112292413078147024219077784550000000000000)
      constant := (62053791567416696898533787486682540657571590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173799821269677800873/50000000000000000000)
  centralHi := (347599642539355601747/100000000000000000000)
  directionLo := (34869100987952833329/10000000000000000000)
  directionHi := (348691009879528333291/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree161.table
  base := (-1896860002954787350892452658169372828493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-49692792215453972931582526360000000000000)
      constant := (968725129722255521540350222184645017372056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree161.table
  base := (-237107500402269597043211654951545670579/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (494)
      previous := (171)
      next := (0)
      square := (5488711190527294572771843600000000000000)
      linear := (-447435967623435040668722345930000000000000)
      constant := (8983637427268777903392877538073134424475760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34869100987952833329/10000000000000000000)
  centralHi := (348691009879528333291/100000000000000000000)
  directionLo := (21861185749530603127/6250000000000000000)
  directionHi := (349778971992489650033/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree162.table
  base := (-3674394501528318114721776756519572791731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-50006432854912675478598060280000000000000)
      constant := (981664834873576378939875309753921708833076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree162.table
  base := (-459299312748067089143052846392657211139/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-3151811133649943545143035058470000000000000)
      constant := (63722621970373929213273674922418391866167560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21861185749530603127/6250000000000000000)
  centralHi := (349778971992489650033/100000000000000000000)
  directionLo := (87715890138788562139/25000000000000000000)
  directionHi := (350863560555154248557/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree163.table
  base := (-3553401357216893533016205348561893544877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-50320073494371378025613594200000000000000)
      constant := (994689620744482583954724052195752425820492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree163.table
  base := (-177670067880600940140015524275427312283/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-3171570493935841805605013695430000000000000)
      constant := (64565271500006225646404160129328406169813300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87715890138788562139/25000000000000000000)
  centralHi := (350863560555154248557/100000000000000000000)
  directionLo := (35194480675634059651/10000000000000000000)
  directionHi := (351944806756340596511/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree164.table
  base := (-686148119330887574658254332545069118963/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-50633714133830080572629128120000000000000)
      constant := (1007799487240257588918404127229098617620740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree164.table
  base := (-3430740596996638666932991239011826157993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-3191329854221740066066992332390000000000000)
      constant := (65413410573977254306049482691154102591291715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35194480675634059651/10000000000000000000)
  centralHi := (351944806756340596511/100000000000000000000)
  directionLo := (353022741307235699839/100000000000000000000)
  directionHi := (551598033292555781/156250000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree165.table
  base := (-330641224317273875035069051663841816819/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-50947354773288783119644662040000000000000)
      constant := (1020994434267574243371700675583446327327240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree165.table
  base := (-3306412243469093441040194604102273037917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-3211089214507638326528970969350000000000000)
      constant := (66267039186570994394012698862644943105710335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353022741307235699839/100000000000000000000)
  centralHi := (551598033292555781/156250000000000000)
  directionLo := (177048697225786578337/50000000000000000000)
  directionHi := (14163895778062926267/4000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree166.table
  base := (-1590208159881670714907777957888593934693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-51260995412747485666660195960000000000000)
      constant := (1034274461734466366252129321236891248522456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree166.table
  base := (-397552040002497902783198235737793658743/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-3230848574793536586990949606310000000000000)
      constant := (67126157332154748886493610644045924428863720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (177048697225786578337/50000000000000000000)
  centralHi := (14163895778062926267/4000000000000000000)
  directionLo := (177584397987767020393/50000000000000000000)
  directionHi := (355168795975534040787/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree167.table
  base := (-3052752849084466171268118317436987860301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-51574636052206188213675729880000000000000)
      constant := (1047639569550301076521361062360252048558796) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree167.table
  base := (-763188212326677271782154627873948110351/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-3250607935079434847452928243270000000000000)
      constant := (67990765005177454519744951945721530851856020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (177584397987767020393/50000000000000000000)
  centralHi := (355168795975534040787/100000000000000000000)
  directionLo := (356236975217379784461/100000000000000000000)
  directionHi := (178118487608689892231/50000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree168.table
  base := (-2923421853467742618036812788229033866593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-51888276691664890760691263800000000000000)
      constant := (1061089757625751855606082158687083864533628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree168.table
  base := (-1461710926830095360264548012920049600481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (494)
      previous := (171)
      next := (0)
      square := (5488711190527294572771843600000000000000)
      linear := (-467195327909333301130700982890000000000000)
      constant := (9837266028595433710138038699879596527966330) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell000.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356236975217379784461/100000000000000000000)
  centralHi := (178118487608689892231/50000000000000000000)
  directionLo := (357301961076825874197/100000000000000000000)
  directionHi := (178650980538412937099/50000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree169.table
  base := (-2792423354924767553109468914733136790471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (57)
      previous := (19)
      next := (0)
      square := (627281278917405094031067840000000000000)
      linear := (-52201917331123593307706797720000000000000)
      constant := (1074625025872772316374341291871067452838116) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree169.table
  base := (-2792423355091409635974107084456128323451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3458)
      previous := (1197)
      next := (0)
      square := (38420978333691062009402905200000000000000)
      linear := (-3290126655651231368376885517190000000000000)
      constant := (69736448911733802769348330783750248560754505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell000.Kernel169
