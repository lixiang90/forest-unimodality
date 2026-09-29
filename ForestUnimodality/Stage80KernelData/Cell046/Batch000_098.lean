import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell046.Parameters
import ForestUnimodality.BinomialMassData.Q47_97.Batch000_049
import ForestUnimodality.BinomialMassData.Q47_97.Batch050_099
import ForestUnimodality.BinomialMassData.Q9237_19012.Batch000_049
import ForestUnimodality.BinomialMassData.Q9237_19012.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree000.table
  base := (338614964958834700381373751/10000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (34)
      previous := (17)
      next := (17)
      square := (713021392226395461788612800000000000000)
      linear := (20453871636894032509657037500000000000)
      constant := (169307482479417350190686875500000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree000.table
  base := (338614964958834700381373751/10000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (34)
      previous := (17)
      next := (17)
      square := (713021392226395461788612800000000000000)
      linear := (20453871636894032509657037500000000000)
      constant := (169307482479417350190686875500000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree001.table
  base := (201599279363458801223894434655398107021249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-12617757152177475737410416889125000000000000)
      constant := (1899811249640054876077381774155115788962931841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree001.table
  base := (201226559636025840407275263745709489306121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-30379959689309420686269442866749125000000000000)
      constant := (4553066588364661268196054051771713790549983266089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49976081004292051691/100000000000000000000)
  directionHi := (12494020251073012923/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree002.table
  base := (30604565435917041248893749643586125185079/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-12810207630409011689293779954962500000000000)
      constant := (582030470993214112733623710625878703732816622) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree002.table
  base := (121987078520019295194250560456715389419967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-61684066575086677013482795175649925000000000000)
      constant := (2785331458837831094515331231462026285324979276703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49976081004292051691/100000000000000000000)
  centralHi := (12494020251073012923/25000000000000000000)
  directionLo := (17669212887631557023/25000000000000000000)
  directionHi := (70676851550526228093/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree003.table
  base := (7605844261225569937584463051356686678929/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-19311536684729285509882351465362500000000000)
      constant := (371712773965832106206845896025987824810214805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree003.table
  base := (75678849298915732463134516782937196484339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-92988173460863933340696147484550725000000000000)
      constant := (1776755670182060202173139543596908670962470708051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17669212887631557023/25000000000000000000)
  centralHi := (70676851550526228093/100000000000000000000)
  directionLo := (43280555731305838149/50000000000000000000)
  directionHi := (86561111462611676299/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree004.table
  base := (48394776002181348287967478816929305376889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-51625731478099118660941845951525000000000000)
      constant := (505002509971882949290707258323187834291148601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree004.table
  base := (24045652389970452464772766932356985465857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-62146140173320594833954749896725762500000000000)
      constant := (603154085525140417899894364451685462372044679713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43280555731305838149/50000000000000000000)
  centralHi := (86561111462611676299/100000000000000000000)
  directionLo := (49976081004292051691/50000000000000000000)
  directionHi := (99952162008584103383/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree005.table
  base := (7862374521057680525209380249941901906797/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-32314194793369833151059494486162500000000000)
      constant := (186864524119003122029608627253594210082105946) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree005.table
  base := (15607542807437267624566303909625227550153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-77798193616209222997561426051176162500000000000)
      constant := (446524726161307287963274579753075217837554374377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49976081004292051691/50000000000000000000)
  centralHi := (99952162008584103383/100000000000000000000)
  directionLo := (22349982874926597339/20000000000000000000)
  directionHi := (13968739296829123337/12500000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree006.table
  base := (20700015741397119638804349854541015170131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-77631047695380213943296131993125000000000000)
      constant := (307052084092118045357527099188226411735762579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree006.table
  base := (410382054877635865717562246029480181303/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-93450247059097851161168102205626562500000000000)
      constant := (367308820134265618218587707242537044778442618175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22349982874926597339/20000000000000000000)
  centralHi := (13968739296829123337/12500000000000000000)
  directionLo := (61207948902257305333/50000000000000000000)
  directionHi := (122415897804514610667/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree007.table
  base := (3396169698454524519914837636873492528703/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-45316852902010380792236637506962500000000000)
      constant := (140434525495946314335737967697747882405133054) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree007.table
  base := (420066497209363851044310505870407614743/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (15675394)
      previous := (7837697)
      next := (7837697)
      square := (328732095693449590098483833924800000000000000)
      linear := (-2226577561265030190301526088981162500000000000)
      constant := (6868898003058553765946669409912649428739639408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61207948902257305333/50000000000000000000)
  centralHi := (122415897804514610667/100000000000000000000)
  directionLo := (33056070459743969243/25000000000000000000)
  directionHi := (132224281838975876973/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree008.table
  base := (8646110141317776810415122373597859965001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-103636363912661309225650418034725000000000000)
      constant := (281467487801775133313465309895382264410694409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree008.table
  base := (8529927526572516746748972537372733831699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-249508707889750214976762909029054725000000000000)
      constant := (675799940324556330521263428632818716346516594291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33056070459743969243/25000000000000000000)
  centralHi := (132224281838975876973/100000000000000000000)
  directionLo := (17669212887631557023/12500000000000000000)
  directionHi := (28270740620210491237/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree009.table
  base := (2525368482718446901668756792815940570241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-58319511010650928433413780527762500000000000)
      constant := (150502153936441181432272294449142684825397569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree009.table
  base := (4952312604130376357381118461639106651607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-280812814775527471303976261337955525000000000000)
      constant := (723806641457608018031647763106577069368413601463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17669212887631557023/12500000000000000000)
  centralHi := (28270740620210491237/20000000000000000000)
  directionLo := (74964121506438077537/50000000000000000000)
  directionHi := (5997129720515046203/4000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree010.table
  base := (2317930946944704252015145404147719479973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-129641680129942404508004704076325000000000000)
      constant := (334957279349572239441189109468375892587065957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree010.table
  base := (1115724618760076371622279331553840685423/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-156058460830652363815594806823428162500000000000)
      constant := (403188678815630744930711754788774830158957161807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74964121506438077537/50000000000000000000)
  centralHi := (5997129720515046203/4000000000000000000)
  directionLo := (79019122251319029157/50000000000000000000)
  directionHi := (31607648900527611663/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree011.table
  base := (167126205384798996064249277170532387919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-142644338238582952149181847097125000000000000)
      constant := (380686557862630409253347993300122539237929871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree011.table
  base := (2220716527639350144061127774392591563/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-171710514273540991979201482977878562500000000000)
      constant := (458610147407224418411697003495119594485661141340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79019122251319029157/50000000000000000000)
  centralHi := (31607648900527611663/20000000000000000000)
  directionLo := (5179747161988893959/3125000000000000000)
  directionHi := (165751909183644606689/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree012.table
  base := (-1568499024495930683251480717218225687391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-155646996347223499790358990117925000000000000)
      constant := (436622517422790372366431337974193714507338081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree012.table
  base := (-205119346880879396223661691152995086949/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-187362567716429620142808159132328962500000000000)
      constant := (526299386240433775239774963655528307955117433836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5179747161988893959/3125000000000000000)
  centralHi := (165751909183644606689/100000000000000000000)
  directionLo := (173122222925223352597/100000000000000000000)
  directionHi := (86561111462611676299/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree013.table
  base := (-186924367997865134385411491689333809343/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-84324827227932023715768066569362500000000000)
      constant := (250903448529111077170178181664847965503133704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree013.table
  base := (-611763204941905240847852432534843478723/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-406029242318636496612829670573558725000000000000)
      constant := (1210233020001623151435289469669570772042886992465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173122222925223352597/100000000000000000000)
  centralHi := (86561111462611676299/50000000000000000000)
  directionLo := (90095661303858426973/50000000000000000000)
  directionHi := (180191322607716853947/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree014.table
  base := (-2082098488495723836113114809267148295857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-90826156282252297536356638079762500000000000)
      constant := (287816640574556420624895285023330401684281487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree014.table
  base := (-528577195005815842033324639201860969073/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (15675394)
      previous := (7837697)
      next := (7837697)
      square := (328732095693449590098483833924800000000000000)
      linear := (-4462585195963405642245336968188362500000000000)
      constant := (14170207343809002930852688951557683017830460028) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90095661303858426973/50000000000000000000)
  centralHi := (180191322607716853947/100000000000000000000)
  directionLo := (186993372651722210291/100000000000000000000)
  directionHi := (46748343162930552573/25000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree015.table
  base := (-5131403405158364920121157978223381838143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-194654970673145142713890419180325000000000000)
      constant := (657700064279735356431204785404021200284912513) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree015.table
  base := (-5192683853703235405945989189601670488231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-468637456090191009267256375191360325000000000000)
      constant := (1586984519013397021559656969354595049335339084921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186993372651722210291/100000000000000000000)
  centralHi := (46748343162930552573/25000000000000000000)
  directionLo := (12097283089895997111/6250000000000000000)
  directionHi := (193556529438335953777/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree016.table
  base := (-296110154592403584623176058564536033519/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-103828814390892845177533781100562500000000000)
      constant := (373863457731314687638728634557462804606197290) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree016.table
  base := (-5980598693637447750783903331927882842757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-499941562975968265594469727500261125000000000000)
      constant := (1804477290341958703835601438928455311348331028187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12097283089895997111/6250000000000000000)
  centralHi := (193556529438335953777/100000000000000000000)
  directionLo := (39980864803433641353/20000000000000000000)
  directionHi := (99952162008584103383/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree017.table
  base := (-819820859844967240514124500097211359899/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-110330143445213118998122352610962500000000000)
      constant := (422753555524123703935726661069778853258841236) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree017.table
  base := (-661421600997716597255944352260741637299/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-265622834930872760960841539904580962500000000000)
      constant := (1020332465673380132579492685952311029750517776545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39980864803433641353/20000000000000000000)
  centralHi := (99952162008584103383/50000000000000000000)
  directionLo := (103028330367560230571/50000000000000000000)
  directionHi := (206056660735120461143/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree018.table
  base := (-1764388282766768537870760581117395133391/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-116831472499533392818710924121362500000000000)
      constant := (475440074439335005888039350338007858379848162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree018.table
  base := (-7110534057500457437972530084066308932557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-562549776747522778248896432118062725000000000000)
      constant := (2295163434301126092646084567979885770807824419987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103028330367560230571/50000000000000000000)
  centralHi := (206056660735120461143/100000000000000000000)
  directionLo := (53007638662894671069/25000000000000000000)
  directionHi := (212030554651578684277/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree019.table
  base := (-1858249400537589720261574483500344716101/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-123332801553853666639299495631762500000000000)
      constant := (531857924175171073261966177871403013132411382) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree019.table
  base := (-1496672390182788226760186528006643438401/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-593853883633300034576109784426963525000000000000)
      constant := (2567660837370436924407031552584665748866460316955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53007638662894671069/25000000000000000000)
  centralHi := (212030554651578684277/100000000000000000000)
  directionLo := (13615042918244484239/6250000000000000000)
  directionHi := (8713627467676469913/4000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree020.table
  base := (-3848255102489011181694962097329369982681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-129834130608173940459888067142162500000000000)
      constant := (591952485896071925943619843026977957832954471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree020.table
  base := (-3872150922668254853368116987732214587507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-312578995259538645451661568367932162500000000000)
      constant := (1428947518081991230295191479399884713163698075437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13615042918244484239/6250000000000000000)
  centralHi := (8713627467676469913/4000000000000000000)
  directionLo := (223499828749265973391/100000000000000000000)
  directionHi := (13968739296829123337/6250000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree021.table
  base := (-3929038346031921378013136464581496448827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-136335459662494214280476638652562500000000000)
      constant := (655676781629336494590983486654740199912986757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree021.table
  base := (-3951670849698535839647426225921658333823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (15675394)
      previous := (7837697)
      next := (7837697)
      square := (328732095693449590098483833924800000000000000)
      linear := (-6698592830661781094189147847395562500000000000)
      constant := (32302452985902912256161159967073068345115910257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223499828749265973391/100000000000000000000)
  centralHi := (13968739296829123337/6250000000000000000)
  directionLo := (45803834827882600671/20000000000000000000)
  directionHi := (57254793534853250839/25000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree022.table
  base := (-1981608425750309762011113936051726555877/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-142836788716814488101065210162962500000000000)
      constant := (722989709853997539569887383201003609671506614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree022.table
  base := (-1992306252514236104506005646922676568271/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-343883102145315901778874920676832962500000000000)
      constant := (1745349691157700576333869416285912451434201449122) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45803834827882600671/20000000000000000000)
  centralHi := (57254793534853250839/25000000000000000000)
  directionLo := (58602149489185942003/25000000000000000000)
  directionHi := (234408597956743768013/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree023.table
  base := (-3954656273686815513490299639368833846507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-149338117771134761921653781673362500000000000)
      constant := (793854898624119862489867824892841142338215637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree023.table
  base := (-3974845764636630569836872884066722803147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-359535155588204529942481596831283362500000000000)
      constant := (1916448578224304175584210097077174480428600894677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58602149489185942003/25000000000000000000)
  centralHi := (234408597956743768013/100000000000000000000)
  directionLo := (119838432346006908471/50000000000000000000)
  directionHi := (239676864692013816943/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree024.table
  base := (-7813605837653755965312009962247253166701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-311678893650910071484484706367525000000000000)
      constant := (1736479843288650941705110647265415594954510291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree024.table
  base := (-1570328441198809633516946618505315957381/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-750374418062186316212176545971467525000000000000)
      constant := (4192077815618313593403010847008803153294811062855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119838432346006908471/50000000000000000000)
  centralHi := (239676864692013816943/100000000000000000000)
  directionLo := (244831795609029221333/100000000000000000000)
  directionHi := (122415897804514610667/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree025.table
  base := (-7645487790984769424134175569033747428047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-324681551759550619125661849388325000000000000)
      constant := (1892231464620128778641552314372836470449505777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree025.table
  base := (-7681258623235675309643373906739211953659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-781678524947963572539389898280368325000000000000)
      constant := (4568101711626959821894221098445154458351981948069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244831795609029221333/100000000000000000000)
  centralHi := (122415897804514610667/50000000000000000000)
  directionLo := (249880405021460258457/100000000000000000000)
  directionHi := (124940202510730129229/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree026.table
  base := (-3705252926322918808786355894617105620617/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-168842104934095583383419496204562500000000000)
      constant := (1027456232665020780440176366539722653215614647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree026.table
  base := (-7444094242087019877003409424931897473791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-812982631833740828866603250589269125000000000000)
      constant := (4960843386185107059505880980310630842282510254881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249880405021460258457/100000000000000000000)
  centralHi := (124940202510730129229/50000000000000000000)
  directionLo := (254829012253778871009/100000000000000000000)
  directionHi := (25482901225377887101/10000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree027.table
  base := (-3556826921496231897380671094155791315889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-175343433988415857204008067714962500000000000)
      constant := (1112237929281332179175206349178900659508800399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree027.table
  base := (-7145147445694010357723086380893572785519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-844286738719518085193816602898169925000000000000)
      constant := (5370189920774120187450910248117985837910185201329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254829012253778871009/100000000000000000000)
  centralHi := (25482901225377887101/10000000000000000000)
  directionLo := (8115104199619844653/3125000000000000000)
  directionHi := (259683334387835028897/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree028.table
  base := (-1351886520803726920448433696586356020573/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-363689526085472262049193278450725000000000000)
      constant := (2400879295895675750694417575155794881012143215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree028.table
  base := (-848615279175413995769883942138930882979/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (15675394)
      previous := (7837697)
      next := (7837697)
      square := (328732095693449590098483833924800000000000000)
      linear := (-8934600465360156546132958726602762500000000000)
      constant := (59143260872492068344406025651284388167121915444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8115104199619844653/3125000000000000000)
  centralHi := (259683334387835028897/100000000000000000000)
  directionLo := (52889712735590350789/20000000000000000000)
  directionHi := (132224281838975876973/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree029.table
  base := (-1587975429296126540078169712353217511611/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-188346092097056404845185210735762500000000000)
      constant := (1292042290363558564488244148611224652866504202) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree029.table
  base := (-6379480061912876590608352720593395858341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-906894952491072597848243307515971525000000000000)
      constant := (6238300567970598049018437530761458090073655743931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52889712735590350789/20000000000000000000)
  centralHi := (132224281838975876973/50000000000000000000)
  directionLo := (6728235815570418927/2500000000000000000)
  directionHi := (269129432622816757081/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree030.table
  base := (-736840561087834454601522655467180888811/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-194847421151376678665773782246162500000000000)
      constant := (1387028622504417083222212407999962180068709204) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree030.table
  base := (-2960242493054151775017740691859157678353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-469099529688424927087728329912436162500000000000)
      constant := (3348445076738174586532864623191547635905908271823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6728235815570418927/2500000000000000000)
  centralHi := (269129432622816757081/100000000000000000000)
  directionLo := (273730269017561931339/100000000000000000000)
  directionHi := (13686513450878096567/5000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree031.table
  base := (-5391207605208527966666530025886958356469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-402697500411393904972724707513125000000000000)
      constant := (2970766176126274526245509767815154608823983179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree031.table
  base := (-5415243477907482786143470330780552992203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-969503166262627110502670012133773125000000000000)
      constant := (7171733625484620770959643423101852744078165097173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273730269017561931339/100000000000000000000)
  centralHi := (13686513450878096567/5000000000000000000)
  directionLo := (139127521404801848631/50000000000000000000)
  directionHi := (278255042809603697263/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree032.table
  base := (-4844336399478376778974573164013177536481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-415700158520034452613901850533925000000000000)
      constant := (3174183285083345873443552092135800012559250271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree032.table
  base := (-4866739849470519826045693379784192023863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-1000807273148404366829883364442673925000000000000)
      constant := (7662763565372545089296212088974835899931182752233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139127521404801848631/50000000000000000000)
  centralHi := (278255042809603697263/100000000000000000000)
  directionLo := (17669212887631557023/6250000000000000000)
  directionHi := (282707406202104912369/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree033.table
  base := (-4256806390232748240607859405730101114179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-428702816628675000255078993554725000000000000)
      constant := (3384283209744406777334457386795560478616689789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree033.table
  base := (-4277667938158012322246097535575674642147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-1032111380034181623157096716751574725000000000000)
      constant := (8169919116636064330262339704680035720228185343677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17669212887631557023/6250000000000000000)
  centralHi := (282707406202104912369/100000000000000000000)
  directionLo := (71772682039403712427/25000000000000000000)
  directionHi := (287090728157614849709/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree034.table
  base := (-726210318327617025101836556650557638477/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-441705474737315547896256136575525000000000000)
      constant := (3601043048470165177858197902745324515897849535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree034.table
  base := (-3650459546042108449799860090017265246813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-1063415486919958879484310069060475525000000000000)
      constant := (8693145342412680375786021184520396163153860295683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71772682039403712427/25000000000000000000)
  centralHi := (287090728157614849709/100000000000000000000)
  directionLo := (58281624845783793149/20000000000000000000)
  directionHi := (145704062114459482873/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree035.table
  base := (-118770799256269136208015820859305785663/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-454708132845956095537433279596325000000000000)
      constant := (3824442120488325658813724532400994796567420825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree035.table
  base := (-2987310022225518246158211557464034090031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (31350788)
      previous := (15675394)
      next := (15675394)
      square := (657464191386899180196967667849600000000000000)
      linear := (-22341216200117063996153539211619925000000000000)
      constant := (188416176480633791050751131487449943009098017729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58281624845783793149/20000000000000000000)
  centralHi := (145704062114459482873/50000000000000000000)
  directionLo := (73915620617010240663/25000000000000000000)
  directionHi := (295662482468040962653/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree036.table
  base := (-227344644561743095727246292167561675949/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-233855395477298321589305211308562500000000000)
      constant := (2027230875002886617187891941621527060954979295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree036.table
  base := (-458040261322698142051189622538149279553/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-1126023700691513392138736773678277125000000000000)
      constant := (9787616258028953548082515508976486558911373305115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73915620617010240663/25000000000000000000)
  centralHi := (295662482468040962653/100000000000000000000)
  directionLo := (74964121506438077537/25000000000000000000)
  directionHi := (299856486025752310149/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree037.table
  base := (-48292920902883394439129246508360170887/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-240356724531618595409893782818962500000000000)
      constant := (2145542535767349396481370778005832926433987472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree037.table
  base := (-312184540976271926787539164681453861473/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-1157327807577290648465950125987177925000000000000)
      constant := (10358775751625758518803585308697445999661893518715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74964121506438077537/25000000000000000000)
  centralHi := (299856486025752310149/100000000000000000000)
  directionLo := (15199631647202815627/5000000000000000000)
  directionHi := (303992632944056312541/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree038.table
  base := (-12291715656454345217702501829748170019/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-246858053585938869230482354329362500000000000)
      constant := (2267148427124498016558524339627309782985319328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree038.table
  base := (-400544814037857941477404931657992524621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-594315957231533952396581739148039362500000000000)
      constant := (5472917317287989219991254092778309224704354267411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15199631647202815627/5000000000000000000)
  centralHi := (303992632944056312541/100000000000000000000)
  directionLo := (308073253556369791113/100000000000000000000)
  directionHi := (154036626778184895557/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree039.table
  base := (120268936118225166439282717961567339/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-253359382640259143051070925839762500000000000)
      constant := (2392041671727339907742186077110129001935463255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree039.table
  base := (-6080250962615980051116300688392443603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-609968010674422580560188415302489762500000000000)
      constant := (5774379979785425519775295535671174841986032634573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308073253556369791113/100000000000000000000)
  centralHi := (154036626778184895557/50000000000000000000)
  directionLo := (78025131459900018307/25000000000000000000)
  directionHi := (312100525839600073229/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree040.table
  base := (408461907147411457411302540052425897721/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-259860711694579416871659497350162500000000000)
      constant := (2520216058737618118779994968560853275271656889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree040.table
  base := (804547972184871020612260007692216866379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-1251240128234622417447590182913880325000000000000)
      constant := (12167521980997532474854294273391619190458319786411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78025131459900018307/25000000000000000000)
  centralHi := (312100525839600073229/100000000000000000000)
  directionLo := (316076489005276116629/100000000000000000000)
  directionHi := (31607648900527611663/10000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree041.table
  base := (165930132329682721560847269526737221213/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-266362040748899690692248068860562500000000000)
      constant := (2651665979217602161701205256013622852571965585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree041.table
  base := (1647847042098345753108281713746676824399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-1282544235120399673774803535222781125000000000000)
      constant := (12802093843745362193595730031203939856110089228591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316076489005276116629/100000000000000000000)
  centralHi := (31607648900527611663/10000000000000000000)
  directionLo := (32000305557048981823/10000000000000000000)
  directionHi := (320003055570489818231/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree042.table
  base := (126362925382504847149335826701544250681/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-272863369803219964512836640370962500000000000)
      constant := (2786386367791132447972001468760723298546575290) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree042.table
  base := (1258331734977850461680149676589087166841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (15675394)
      previous := (7837697)
      next := (7837697)
      square := (328732095693449590098483833924800000000000000)
      linear := (-13406615734756907450020580485017162500000000000)
      constant := (137269911247838747824125772437249340586487541481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32000305557048981823/10000000000000000000)
  centralHi := (320003055570489818231/100000000000000000000)
  directionLo := (20242626381965216751/6250000000000000000)
  directionHi := (323882022111443468017/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree043.table
  base := (3419823001438464794762503036395789108969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-558729397715080476666850423762725000000000000)
      constant := (5848745299925512737038416024638272979726289321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree043.table
  base := (3410028306490444954542408185439510982403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-1345152448891954186429230239840582725000000000000)
      constant := (14118572467084437899749583070904261330309065014627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20242626381965216751/6250000000000000000)
  centralHi := (323882022111443468017/100000000000000000000)
  directionLo := (327715078871182118173/100000000000000000000)
  directionHi := (163857539435591059087/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree044.table
  base := (271007291830496514093877224652270635131/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-285866027911860512154013783391762500000000000)
      constant := (3065620694544607003639831590546875715247580632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree044.table
  base := (1081766689161086137494759547058432575813/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-688228277888865721378221796074741762500000000000)
      constant := (7400218787815525164311102337455788485192169330634) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327715078871182118173/100000000000000000000)
  centralHi := (163857539435591059087/50000000000000000000)
  directionLo := (5179747161988893959/1562500000000000000)
  directionHi := (331503818367289213377/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree045.table
  base := (1318836618591303415210947157100473578527/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-292367356966180785974602354902162500000000000)
      constant := (3210126770694901991987288406354004211800721086) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree045.table
  base := (2633494515114555279358898315319062052643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-703880331331754349541828472229192162500000000000)
      constant := (7749014392885391410739211324058286409327816486787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5179747161988893959/1562500000000000000)
  centralHi := (331503818367289213377/100000000000000000000)
  directionLo := (335249743123898960087/100000000000000000000)
  directionHi := (41906217890487370011/12500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree046.table
  base := (779599528937852106662778794504578578069/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-298868686020501059795190926412562500000000000)
      constant := (3357887509120521035645282775470899319364204884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree046.table
  base := (3114541040894656548721675173286518958897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-719532384774642977705435148383642562500000000000)
      constant := (8105664994543667176362695674563172453129112757073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335249743123898960087/100000000000000000000)
  centralHi := (41906217890487370011/12500000000000000000)
  directionLo := (16947713631725357227/5000000000000000000)
  directionHi := (338954272634507144541/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree047.table
  base := (7219819159599548385919853664619063745081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-610740030149642667231558995845925000000000000)
      constant := (7017799734079547027459476211371525770777467129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree047.table
  base := (7212702153191230729687986179527265927909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-1470368876435063211738083649076185925000000000000)
      constant := (16940326642434912198188375741812730174072785570181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16947713631725357227/5000000000000000000)
  centralHi := (338954272634507144541/100000000000000000000)
  directionLo := (85654687411772509399/25000000000000000000)
  directionHi := (342618749647090037597/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree048.table
  base := (8223831155797926862532571471797529564329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-623742688258283214872736138866725000000000000)
      constant := (7326322193081532810024800898639342955670771561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree048.table
  base := (2054317010224223314875297022391582041029/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-750836491660420234032648500692543362500000000000)
      constant := (8842502807919579620664462977381462212826249016522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85654687411772509399/25000000000000000000)
  centralHi := (342618749647090037597/100000000000000000000)
  directionLo := (69248889170089341039/20000000000000000000)
  directionHi := (86561111462611676299/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree049.table
  base := (924830472146974722237245721877343630941/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-318372673183461881256956640943762500000000000)
      constant := (3820668716006203318784887095876757131117619345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree049.table
  base := (9242255017483572578237233734825766867049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-638474423243072771508750667927525000000000000)
      constant := (7682363621481943392186619532170081890452064041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69248889170089341039/20000000000000000000)
  centralHi := (86561111462611676299/25000000000000000000)
  directionLo := (4372907087875554523/1250000000000000000)
  directionHi := (349832567030044361841/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree050.table
  base := (2058552695366364374239096628067529934377/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-649748004475564310155090424908325000000000000)
      constant := (7962840968614788498020154033471186945762765965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree050.table
  base := (5143594671911768482553110982239718167923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-782140598546197490359861853001444162500000000000)
      constant := (9610682129103487244333934111868816469539012004307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4372907087875554523/1250000000000000000)
  centralHi := (349832567030044361841/100000000000000000000)
  directionLo := (17669212887631557023/5000000000000000000)
  directionHi := (353384257752631140461/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree051.table
  base := (709798575446396120248575800031115021369/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-331375331292102428898133783964562500000000000)
      constant := (4145414377499086336970372750683054589888487368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree051.table
  base := (5675821657261493650597649034322729124331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-797792651989086118523468529155894562500000000000)
      constant := (10006511781314621894486378882394044741927323739979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17669212887631557023/5000000000000000000)
  centralHi := (353384257752631140461/100000000000000000000)
  directionLo := (356900605631211563437/100000000000000000000)
  directionHi := (178450302815605781719/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree052.table
  base := (12439957388960063183603666086845113449789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-675753320692845405437444710949925000000000000)
      constant := (8625297135545500611588903156560625672449064701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree052.table
  base := (2487046156959964560651875656140683025931/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-1626889410863949493374150410620689925000000000000)
      constant := (20820324245044706243721545383314260502524772271895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356900605631211563437/100000000000000000000)
  centralHi := (178450302815605781719/50000000000000000000)
  directionLo := (360382645215433707893/100000000000000000000)
  directionHi := (180191322607716853947/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree053.table
  base := (6770976574971445567683021385661718263941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-344377989400742976539310926985362500000000000)
      constant := (4483121404449452715383865948854478607145420869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree053.table
  base := (3384400783004238954919797548092805388233/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-829096758874863374850681881464795362500000000000)
      constant := (10821629214858114901021355615883596864346640394194) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360382645215433707893/100000000000000000000)
  centralHi := (180191322607716853947/50000000000000000000)
  directionLo := (181915680773415410401/50000000000000000000)
  directionHi := (363831361546830820803/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree054.table
  base := (733122381008583436905495275478714291761/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-350879318455063250359899498495762500000000000)
      constant := (4656831396814658910256504811919017227711792490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree054.table
  base := (7329222804817373443784269873503132959521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-844748812317752003014288557619245762500000000000)
      constant := (11240909503100952374986719067118764706966735546689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181915680773415410401/50000000000000000000)
  centralHi := (363831361546830820803/100000000000000000000)
  directionLo := (45905961676692979/12500000000000000)
  directionHi := (367247693413543832001/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree055.table
  base := (493786082408038966611110407358536453189/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-357380647509383524180488070006162500000000000)
      constant := (4833777198616468238658282218777446011808884816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree055.table
  base := (3949368513862684751618000208345134936613/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-860400865760640631177895233773696162500000000000)
      constant := (11667999777495428960797162277673840308793477425034) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45905961676692979/12500000000000000)
  centralHi := (367247693413543832001/100000000000000000000)
  directionLo := (185316268167500506767/50000000000000000000)
  directionHi := (74126507267000202707/20000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree056.table
  base := (8478907884782915205542884482031421843347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-363881976563703798001076641516562500000000000)
      constant := (5013957594066082210578626757216733648124051923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree056.table
  base := (8477215959850198949820434970699516023613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (15675394)
      previous := (7837697)
      next := (7837697)
      square := (328732095693449590098483833924800000000000000)
      linear := (-17878631004153658353908202243431562500000000000)
      constant := (246997900820051528318148286156762850567042561133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185316268167500506767/50000000000000000000)
  centralHi := (74126507267000202707/20000000000000000000)
  directionLo := (186993372651722210291/50000000000000000000)
  directionHi := (373986745303444420583/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree057.table
  base := (18132197630818359785612882003013778468323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-740766611236048143643330426053925000000000000)
      constant := (10394742970389856582224332390744231641608451107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree057.table
  base := (1812908758193789814038384033150451189021/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-891704972646417887505108586082596962500000000000)
      constant := (12545598974892452042249624223753833783951170560945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186993372651722210291/50000000000000000000)
  centralHi := (373986745303444420583/100000000000000000000)
  directionLo := (188655568653042261729/50000000000000000000)
  directionHi := (377311137306084523459/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree058.table
  base := (9662044725559222574392182213462321841591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-376884634672344345642253784537362500000000000)
      constant := (5384017880436969813944465160649441986207529719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree058.table
  base := (2415153991079524101867650567355786164043/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-907357026089306515668715262237047362500000000000)
      constant := (12996102919582424655492152996303298066985883557548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188655568653042261729/50000000000000000000)
  centralHi := (377311137306084523459/100000000000000000000)
  directionLo := (380606493648963547301/100000000000000000000)
  directionHi := (190303246824481773651/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree059.table
  base := (10266650443085756194092003660694756600971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-383385963726664619462842356047762500000000000)
      constant := (5573895884317472955163661598210889464858536139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree059.table
  base := (20530676166172293045673857304187109641541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-1846018159064390287664643876782995525000000000000)
      constant := (26908813683466449370292059752996168900346039504869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380606493648963547301/100000000000000000000)
  centralHi := (190303246824481773651/50000000000000000000)
  directionLo := (383873562101255014149/100000000000000000000)
  directionHi := (7677471242025100283/2000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree060.table
  base := (21759660037703507189605305468314177317793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-779774585561969786566861855116325000000000000)
      constant := (11534009376282014852497142008515868094383114337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree060.table
  base := (2719656230790675183158638426888452412891/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-938661132975083771995928614545948162500000000000)
      constant := (13920508816046207097555186207841199669322769188076) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383873562101255014149/100000000000000000000)
  centralHi := (7677471242025100283/2000000000000000000)
  directionLo := (387113058876671907553/100000000000000000000)
  directionHi := (193556529438335953777/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree061.table
  base := (11501505832948085698452110435976700138581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-396388621835305167104019499068562500000000000)
      constant := (5963343561581848231703613752039592271603908629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree061.table
  base := (23000799083638047570781830146134210093613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-1908626372835944800319070581400797125000000000000)
      constant := (28788814208614989100189976141485990636682702125517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387113058876671907553/100000000000000000000)
  centralHi := (193556529438335953777/50000000000000000000)
  directionLo := (97581417616714175943/25000000000000000000)
  directionHi := (390325670466856703773/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree062.table
  base := (6065803893762634043242488613529356516457/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-402889950889625440924608070578962500000000000)
      constant := (6162911845089329572634602087292520430926687826) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree062.table
  base := (24261184945996912386008412418393140221187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-1939930479721722056646283933709697925000000000000)
      constant := (29752200274417551707519584321509588383775097507683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97581417616714175943/25000000000000000000)
  centralHi := (390325670466856703773/100000000000000000000)
  directionLo := (39351205534004771129/10000000000000000000)
  directionHi := (393512055340047711291/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree063.table
  base := (12770072577845805604373647478539309254923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-409391279943945714745196642089362500000000000)
      constant := (6365708943029176357132585768654738860779570507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree063.table
  base := (6384570500400398234979434261251463433433/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (15675394)
      previous := (7837697)
      next := (7837697)
      square := (328732095693449590098483833924800000000000000)
      linear := (-20114638638852033805852013122638762500000000000)
      constant := (313583397917032349258949043348003718780626767506) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39351205534004771129/10000000000000000000)
  centralHi := (393512055340047711291/100000000000000000000)
  directionLo := (396672845516927630917/100000000000000000000)
  directionHi := (198336422758463815459/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree064.table
  base := (670842151698850553883400124099760526989/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-415892608998265988565785213599762500000000000)
      constant := (6571734317489491931573163629198692935968790020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree064.table
  base := (6707994251781272720961845211574809376343/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-1001269346746638284650355319163749762500000000000)
      constant := (15862864907344412625062311990628257445588498200174) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396672845516927630917/100000000000000000000)
  centralHi := (198336422758463815459/50000000000000000000)
  directionLo := (399808648034336413531/100000000000000000000)
  directionHi := (99952162008584103383/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree065.table
  base := (7035933763139369111008883192633134454101/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-422393938052586262386373785110162500000000000)
      constant := (6780987482686992159566883923431407824157272618) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree065.table
  base := (28142167723346419450800227361049245268113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-2033842800379053825627923990636400325000000000000)
      constant := (32735868421189355310720324760016479155545148196017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399808648034336413531/100000000000000000000)
  centralHi := (99952162008584103383/25000000000000000000)
  directionLo := (80584009261289911323/20000000000000000000)
  directionHi := (50365005788306194577/12500000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree066.table
  base := (14735099428503848926088743919915821326741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-428895267106906536206962356620562500000000000)
      constant := (6993467999915317718624203208072162962863306069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree066.table
  base := (3683595230733606466274324233699309130997/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-1032573453632415540977568671472650562500000000000)
      constant := (16880793365060651605978307797414620989738541623892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80584009261289911323/20000000000000000000)
  centralHi := (50365005788306194577/12500000000000000000)
  directionLo := (406007601392066323263/100000000000000000000)
  directionHi := (6343868771751036301/1562500000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree067.table
  base := (30812993265856659033295959532171608300043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-870793192322453620055101856261925000000000000)
      constant := (14418350945965786728187345213032827662495104587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree067.table
  base := (38514595049676153681661519456863057451/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-1048225507075304169141175347627100962500000000000)
      constant := (17401441429432015199249927611070516486432223223600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406007601392066323263/100000000000000000000)
  centralHi := (6343868771751036301/1562500000000000000)
  directionLo := (25566990823487752411/6250000000000000000)
  directionHi := (409071853175804038577/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree068.table
  base := (16086021112469009073949681940431408041487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-441897925215547083848139499641362500000000000)
      constant := (7428109544092893540791403961992869118262351183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree068.table
  base := (16085417533941968648300833092059219517061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-1063877560518192797304782023781551362500000000000)
      constant := (17929877553868007459916481516893007069142900704549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25566990823487752411/6250000000000000000)
  centralHi := (409071853175804038577/100000000000000000000)
  directionLo := (82422664294048184457/20000000000000000000)
  directionHi := (206056660735120461143/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree069.table
  base := (1048352407827215082876699602139661968409/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-448399254269867357668728071151762500000000000)
      constant := (7650269890122471039744463000588300771372164496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree069.table
  base := (33546171004210780056347498969543899217439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-2159059227922162850936777399872003525000000000000)
      constant := (36932201942218411432359238964120847184366257405951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82422664294048184457/20000000000000000000)
  centralHi := (206056660735120461143/50000000000000000000)
  directionLo := (207566253522689532099/50000000000000000000)
  directionHi := (415132507045379064199/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree070.table
  base := (17469317857403770884544926258080610822379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-454900583324187631489316642662162500000000000)
      constant := (7875656219262557205604000169264905467227764011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree070.table
  base := (17468811261603278901403825759444664752563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (15675394)
      previous := (7837697)
      next := (7837697)
      square := (328732095693449590098483833924800000000000000)
      linear := (-22350646273550409257795824001845962500000000000)
      constant := (387961448743938378052588604475209846432186398083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207566253522689532099/50000000000000000000)
  centralHi := (415132507045379064199/100000000000000000000)
  directionLo := (418129892591200969279/100000000000000000000)
  directionHi := (1306655914347503029/312500000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree071.table
  base := (7269212440279561201862647720497339512481/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-922803824757015810619810428345125000000000000)
      constant := (16208536535966583343831514005754522337364668645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree071.table
  base := (9086283564635311713233166573815638050471/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-1110833720846858681795602052244902562500000000000)
      constant := (19561906980508701954111156207237059208952865630478) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418129892591200969279/100000000000000000000)
  centralHi := (1306655914347503029/312500000000000000)
  directionLo := (105276485904639699149/25000000000000000000)
  directionHi := (421105943618558796597/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree072.table
  base := (37769505922262354851261535840549684804579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-935806482865656358260987571365925000000000000)
      constant := (16672211596587051450573021544706731984326283811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree072.table
  base := (18884328112003242463159922311149212672653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-1126485774289747309959208728399352962500000000000)
      constant := (20121488382656928510706644301204727288830817976877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105276485904639699149/25000000000000000000)
  centralHi := (421105943618558796597/100000000000000000000)
  directionLo := (53007638662894671069/12500000000000000000)
  directionHi := (424061109303157368553/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree073.table
  base := (9802230297979376696675305377789821262291/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-474404570487148452951082357193362500000000000)
      constant := (8571168595265901386060776870060786356513792038) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree073.table
  base := (1960407164536022203697195191252651652877/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-1142137827732635938122815404553803362500000000000)
      constant := (20688854685144172426796865050119685675765091828930) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53007638662894671069/12500000000000000000)
  centralHi := (424061109303157368553/100000000000000000000)
  directionLo := (106748955819240903523/25000000000000000000)
  directionHi := (426995823276963614093/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree074.table
  base := (20332133376140424255695462275647083398493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-480905899541468726771670928703762500000000000)
      constant := (8809456464801769940848751765833538407696420637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree074.table
  base := (20331777357566595261227592253118897790977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-1157789881175524566286422080708253762500000000000)
      constant := (21264005427751482079470245396186393929316041525793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106748955819240903523/25000000000000000000)
  centralHi := (426995823276963614093/100000000000000000000)
  directionLo := (429910504370990570709/100000000000000000000)
  directionHi := (42991050437099057071/10000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree075.table
  base := (42135505343617296269193452090557077700729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-974814457191578001184519000428325000000000000)
      constant := (18101938463225415376239376071625676544086159161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree075.table
  base := (21067426856448111774928434381110880275777/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-1173441934618413194450028756862704162500000000000)
      constant := (21846940194981083449253217033788708060683000688993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429910504370990570709/100000000000000000000)
  centralHi := (42991050437099057071/10000000000000000000)
  directionLo := (432805557313058381493/100000000000000000000)
  directionHi := (216402778656529190747/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree076.table
  base := (21811301658531962429508173080870626280191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-493908557650109274412848071724562500000000000)
      constant := (9295706737397638996265046211491961722670317119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree076.table
  base := (43622007074139547058121656434013566875479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-2378187976122603645227270866034309125000000000000)
      constant := (44875317223421481101611060305715780870406047968311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432805557313058381493/100000000000000000000)
  centralHi := (216402778656529190747/50000000000000000000)
  directionLo := (435681373383823495649/100000000000000000000)
  directionHi := (8713627467676469913/2000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree077.table
  base := (45125530284704267019977716895046243534593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-1000819773408859096466873286469925000000000000)
      constant := (19087337678393221690112014883956865105416985537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree077.table
  base := (141015577550414626530526759775152729623/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (15675394)
      previous := (7837697)
      next := (7837697)
      square := (328732095693449590098483833924800000000000000)
      linear := (-24586653908248784709739634881053162500000000000)
      constant := (470125721209599720789857056847183780963898806880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435681373383823495649/100000000000000000000)
  centralHi := (8713627467676469913/2000000000000000000)
  directionLo := (219269165517043335797/50000000000000000000)
  directionHi := (87707666206817334319/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree078.table
  base := (46644258803553253811543417551884896084909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-1013822431517499644108050429490725000000000000)
      constant := (19589710815808199955323657667881134987262908781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree078.table
  base := (11660939967424247266350469729120148110251/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-1220398094947079078940848785326055362500000000000)
      constant := (23642445071899991672491093182980361099830026666518) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219269165517043335797/50000000000000000000)
  centralHi := (87707666206817334319/20000000000000000000)
  directionLo := (220688398233068510567/50000000000000000000)
  directionHi := (88275359293227404227/20000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree079.table
  base := (24089382045083297753712675838606511753047/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-513412544813070095874613786255762500000000000)
      constant := (10049266326926392733065188037605611169084419223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree079.table
  base := (12044576949022423961652012209660053306907/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-1236050148389967707104455461480505762500000000000)
      constant := (24256512533551627600919475812343729449268631598326) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220688398233068510567/50000000000000000000)
  centralHi := (88275359293227404227/20000000000000000000)
  directionLo := (444197124181660260817/100000000000000000000)
  directionHi := (222098562090830130409/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree080.table
  base := (49729023762906859263794799977543846760243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-1039827747734780739390404715532325000000000000)
      constant := (20613802981938151616904585686114710054167126387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree080.table
  base := (12432151632849655348660751286115923993961/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-1251702201832856335268062137634956162500000000000)
      constant := (24878362475002274793533002581982957077981777793298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444197124181660260817/100000000000000000000)
  centralHi := (222098562090830130409/50000000000000000000)
  directionLo := (446999657498531946783/100000000000000000000)
  directionHi := (13968739296829123337/3125000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree081.table
  base := (12823754402296523976326588151951694948457/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-526415202921710643515790929276562500000000000)
      constant := (10567760804942029196927730769679664495540063826) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree081.table
  base := (51294636155774413639007025781216217418873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-2534708510551489926863337627578813125000000000000)
      constant := (51015989342494370509394519128405257104905716712857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446999657498531946783/100000000000000000000)
  centralHi := (13968739296829123337/3125000000000000000)
  directionLo := (449784729038628465223/100000000000000000000)
  directionHi := (56223091129828558153/12500000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree082.table
  base := (26438363687632297097158934436534668968451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-532916531976030917336379500786962500000000000)
      constant := (10831844182970534426974014366573229700324155459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree082.table
  base := (52876378685086789982313503761234054029247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-2566012617437267183190550979887713925000000000000)
      constant := (52290817838293068897494389303067713678181205240223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449784729038628465223/100000000000000000000)
  centralHi := (56223091129828558153/12500000000000000000)
  directionLo := (452552661188617903559/100000000000000000000)
  directionHi := (11313816529715447589/2500000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree083.table
  base := (27237068288209948850371119203405160177189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-539417861030351191156968072297362500000000000)
      constant := (11099151547502214702315798823018751652107171301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree083.table
  base := (54473817882825832259481615473376031637501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-2597316724323044439517764332196614725000000000000)
      constant := (53581210070601503061509011316026581109857069828509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452552661188617903559/100000000000000000000)
  centralHi := (11313816529715447589/2500000000000000000)
  directionLo := (91060753307107568693/20000000000000000000)
  directionHi := (227651883267768921733/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree084.table
  base := (28043615162756022970271423999065729607671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-545919190084671464977556643807762500000000000)
      constant := (11369682828500520078855933892165559449878576439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree084.table
  base := (14021734772570276395141804148274727060897/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (15675394)
      previous := (7837697)
      next := (7837697)
      square := (328732095693449590098483833924800000000000000)
      linear := (-26822661542947160161683445760260362500000000000)
      constant := (560073119472087894269854520340293919377766027554) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91060753307107568693/20000000000000000000)
  centralHi := (227651883267768921733/50000000000000000000)
  directionLo := (45803834827882600671/10000000000000000000)
  directionHi := (458038348278826006711/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree085.table
  base := (28857997589081150253901059747007228947571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-552420519138991738798145215318162500000000000)
      constant := (11643437962716370781763780327592778517167695539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree085.table
  base := (1803616533538204019907249656764392058001/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-1329962469047299476086095518407208162500000000000)
      constant := (28104342226153894876696331706951681435414265808144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45803834827882600671/10000000000000000000)
  centralHi := (458038348278826006711/100000000000000000000)
  directionLo := (460756700620341138311/100000000000000000000)
  directionHi := (57594587577542642289/12500000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree086.table
  base := (59360418992935377740410550960567578208943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-1117843696386624025237467573657125000000000000)
      constant := (23840833786060769038101887954904830343367944687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree086.table
  base := (59360175883479504896906723540361083501587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-2691229044980376208499404389123317125000000000000)
      constant := (57545766032809801926560687384860145638134103431283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460756700620341138311/100000000000000000000)
  centralHi := (57594587577542642289/12500000000000000000)
  directionLo := (463459109133794275837/100000000000000000000)
  directionHi := (231729554566897137919/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree087.table
  base := (1220409816101424570273786487941095594143/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-565423177247632286439322358338962500000000000)
      constant := (12200619567858847639610373342460006711132287175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree087.table
  base := (61020268733970636154639282105277867922539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-2722533151866153464826617741432217925000000000000)
      constant := (58898410206079597207355602705347233605488889851851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463459109133794275837/100000000000000000000)
  centralHi := (231729554566897137919/50000000000000000000)
  directionLo := (14567057847340734811/3125000000000000000)
  directionHi := (466145851114903513953/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree088.table
  base := (31348100356226652720141134513806120520993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-571924506301952560259910929849362500000000000)
      constant := (12484045940617252846258251317200501787982023137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree088.table
  base := (1959249933933656614221992620226062161029/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-1376918629375965360576915546870559362500000000000)
      constant := (30133308376053714966769081676406708312029849412176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14567057847340734811/3125000000000000000)
  centralHi := (466145851114903513953/100000000000000000000)
  directionLo := (18752687836539501441/4000000000000000000)
  directionHi := (234408597956743768013/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree089.table
  base := (12877507954525500647809418731655431332579/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-1156851670712545668160999002719525000000000000)
      constant := (25541391938471649601398887985503804767041179055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree089.table
  base := (1609683863669476716441164216257294073709/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-1392570682818853988740522223025009762500000000000)
      constant := (30825192736131835315729099590578572712821133647620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18752687836539501441/4000000000000000000)
  centralHi := (234408597956743768013/50000000000000000000)
  directionLo := (235736702624311831667/50000000000000000000)
  directionHi := (94294681049724732667/20000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree090.table
  base := (66094499909800872506587599095922384527459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-1169854328821186215802176145740325000000000000)
      constant := (26121139231443991144931347900020283716018861731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree090.table
  base := (16523582694672920517712067026939492183119/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-1408222736261742616904128899179460162500000000000)
      constant := (31524858093610612949154664030233978901978541954142) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235736702624311831667/50000000000000000000)
  centralHi := (94294681049724732667/20000000000000000000)
  directionLo := (14816085422122317967/3125000000000000000)
  directionHi := (94822946701582834989/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree091.table
  base := (67817073830852985543306185528144298582521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-1182856986929826763443353288761125000000000000)
      constant := (26707333691530560218888368561315534705362940089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree091.table
  base := (33908459707517830417278125248073417882803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (15675394)
      previous := (7837697)
      next := (7837697)
      square := (328732095693449590098483833924800000000000000)
      linear := (-29058669177645535613627256639467562500000000000)
      constant := (657802129949794293159580844876806951029105377923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14816085422122317967/3125000000000000000)
  centralHi := (94822946701582834989/20000000000000000000)
  directionLo := (29796339251989341811/6250000000000000000)
  directionHi := (476741428031829468977/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree092.table
  base := (69555254949486554412690465184269873113319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-1195859645038467311084530431781925000000000000)
      constant := (27299975256760885641075304912855295236123218471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree092.table
  base := (4347194624104830605828781725784715720621/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-1439526843147519873231342251488360962500000000000)
      constant := (32947531484836333066453159749316331046755923972712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29796339251989341811/6250000000000000000)
  centralHi := (476741428031829468977/100000000000000000000)
  directionLo := (95870745876805526777/20000000000000000000)
  directionHi := (239676864692013816943/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree093.table
  base := (14261807463545708126277903214758281550039/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-1208862303147107858725707574802725000000000000)
      constant := (27899063871170489092402308129630878355521584755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree093.table
  base := (35654454324625967167427300590881183359211/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (768094306)
      previous := (384047153)
      next := (384047153)
      square := (16107872688979029914825707862315200000000000000)
      linear := (-1455178896590408501394948927642811362500000000000)
      constant := (33670539379518690541042506403275614121823585933899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95870745876805526777/20000000000000000000)
  centralHi := (239676864692013816943/50000000000000000000)
  directionLo := (240975935804243303429/50000000000000000000)
  directionHi := (481951871608486606859/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree094.table
  base := (9134801945508679117283770383292602272981/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-610932480627874203183442358911762500000000000)
      constant := (14252299742109418790706688083420325379145912916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree094.table
  base := (73078298132063908024468778831262403070261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-2941661900066594259117111207594523525000000000000)
      constant := (68802655984035878854886379532007743816621893883349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240975935804243303429/50000000000000000000)
  centralHi := (481951871608486606859/100000000000000000000)
  directionLo := (484536082474226804123/100000000000000000000)
  directionHi := (121134020618556701031/25000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree095.table
  base := (74863384837597399321406257288623077420071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-1234867619364388954008061860844325000000000000)
      constant := (29116582050263701680708295889735779535445448039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree095.table
  base := (74863277672923575558914185114295176239519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-2972966006952371515444324559903424325000000000000)
      constant := (70279794537108081551728463412904745948833559884671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484536082474226804123/100000000000000000000)
  centralHi := (121134020618556701031/25000000000000000000)
  directionLo := (60888322963543556861/12500000000000000000)
  directionHi := (487106583708348454889/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree096.table
  base := (38331970378773179857502374554726592195367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-623935138736514750824619501932562500000000000)
      constant := (14867505764043226671474010247168222505966208103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree096.table
  base := (76663842973344764901315194901069341887429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1536188612)
      previous := (768094306)
      next := (768094306)
      square := (32215745377958059829651415724630400000000000000)
      linear := (-3004270113838148771771537912212325125000000000000)
      constant := (71772494321146849373750658870054492212202985525861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60888322963543556861/12500000000000000000)
  centralHi := (487106583708348454889/100000000000000000000)
  directionLo := (244831795609029221333/50000000000000000000)
  directionHi := (489663591218058442667/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree097.table
  base := (78480079367733324773922217100669223915327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (68)
      previous := (34)
      next := (34)
      square := (1426042784452790923577225600000000000000)
      linear := (-134007113995288558751239892325000000000000)
      constant := (3226685926290080435900105805975669223915327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree097.table
  base := (7847999015258161763167247201705958996483/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (81634)
      previous := (40817)
      next := (40817)
      square := (1711964362735575503754459332800000000000000)
      linear := (-161312265954082582001209016076162500000000000)
      constant := (3894184039137114343005315927300683162752778415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell046.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244831795609029221333/50000000000000000000)
  centralHi := (489663591218058442667/100000000000000000000)
  directionLo := (98441463060463176369/20000000000000000000)
  directionHi := (246103657651157940923/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 47
  qDenominator := 97
  table := BinomialMassData.Q47_97.Degree098.table
  base := (8031179709541118933112402299711738054929/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (319906)
      previous := (159953)
      next := (159953)
      square := (6708818279458154899969057835200000000000000)
      linear := (-636937796845155298465796644953362500000000000)
      constant := (15495605536889232301749946040282413716794134805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47_97.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree098.table
  base := (80311715707034622668857782208917500844663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (639812)
      previous := (319906)
      next := (319906)
      square := (13417636558916309799938115670400000000000000)
      linear := (-1277333747442608614921268061986725000000000000)
      constant := (31155592353171319643177519572012717265447434167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell046.Kernel098
